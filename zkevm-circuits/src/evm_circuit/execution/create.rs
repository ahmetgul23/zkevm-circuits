use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{
            N_BYTES_ACCOUNT_ADDRESS, N_BYTES_GAS, N_BYTES_MEMORY_ADDRESS, N_BYTES_MEMORY_WORD_SIZE,
            N_BYTES_U64,
        },
        step::ExecutionState,
        util::{
            and,
            common_gadget::TransferGadget,
            constraint_builder::{
                ConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition::{Any, Delta, To},
            },
            from_bytes,
            math_gadget::{ConstantDivisionGadget, IsZeroGadget},
            memory_gadget::{MemoryAddressGadget, MemoryExpansionGadget},
            not, rlc, select, sum, CachedRegion, Cell, RandomLinearCombination, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{AccountFieldTag, CallContextFieldTag},
    util::Expr,
};
use bus_mapping::{circuit_input_builder::CopyDataType, evm::OpcodeId};
use eth_types::{evm_types::GasCost, Field, ToBigEndian, ToLittleEndian, ToScalar, U256};
use ethers_core::utils::{keccak256, rlp};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};
use keccak256::EMPTY_HASH_LE;
use std::iter::once;

/// Gadget for CREATE and CREATE2 opcodes
#[derive(Clone, Debug)]
pub(crate) struct CreateGadget<F> {
    opcode: Cell<F>,
    is_create2: Cell<F>,

    value: Word<F>,
    salt: Word<F>,
    new_address: RandomLinearCombination<F, N_BYTES_ACCOUNT_ADDRESS>,

    // tx access list for new address
    tx_id: Cell<F>,
    reversion_info: ReversionInfo<F>,
    was_warm: Cell<F>,

    caller_address: RandomLinearCombination<F, N_BYTES_ACCOUNT_ADDRESS>,
    nonce: RlpU64Gadget<F>,

    callee_reversion_info: ReversionInfo<F>,
    callee_is_success: Cell<F>,

    transfer: TransferGadget<F>,

    initialization_code: MemoryAddressGadget<F>,
    initialization_code_word_size: ConstantDivisionGadget<F, N_BYTES_MEMORY_ADDRESS>,
    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_WORD_SIZE>,

    gas_left: ConstantDivisionGadget<F, N_BYTES_GAS>,

    code_hash: Cell<F>,

    keccak_input: Cell<F>,
    keccak_input_length: Cell<F>,
    keccak_output: Word<F>,
}

impl<F: Field> ExecutionGadget<F> for CreateGadget<F> {
    const NAME: &'static str = "CREATE";

    const EXECUTION_STATE: ExecutionState = ExecutionState::CREATE;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        // Use rw_counter of the step which triggers next call as its call_id.
        let callee_call_id = cb.curr.state.rw_counter.clone();

        let opcode = cb.query_cell();
        cb.opcode_lookup(opcode.expr(), 1.expr());

        let is_create2 = cb.query_bool();
        cb.require_equal(
            "Opcode is CREATE or CREATE2",
            opcode.expr(),
            select::expr(
                is_create2.expr(),
                OpcodeId::CREATE2.expr(),
                OpcodeId::CREATE.expr(),
            ),
        );

        let value = cb.query_word();
        cb.stack_pop(value.expr());

        let initialization_code = MemoryAddressGadget::construct_2(cb);
        cb.stack_pop(initialization_code.offset()); // are these rlc or not?
        cb.stack_pop(initialization_code.length());

        let salt = cb.condition(is_create2.expr(), |cb| {
            let salt = cb.query_word();
            cb.stack_pop(salt.expr());
            salt
        });
        let new_address = cb.query_rlc();
        let callee_is_success = cb.query_bool();
        cb.stack_push(callee_is_success.expr() * new_address.expr());

        let code_hash = cb.query_cell();
        cb.condition(initialization_code.has_length(), |cb| {
            cb.copy_table_lookup(
                cb.curr.state.call_id.expr(),
                CopyDataType::Memory.expr(),
                code_hash.expr(),
                CopyDataType::Bytecode.expr(),
                initialization_code.offset(),
                initialization_code.address(),
                0.expr(),
                initialization_code.length(),
                0.expr(),
                initialization_code.length(),
            );
        });
        cb.condition(not::expr(initialization_code.has_length()), |cb| {
            cb.require_equal(
                "",
                code_hash.expr(),
                Word::random_linear_combine_expr(
                    (*EMPTY_HASH_LE).map(|b| b.expr()),
                    cb.power_of_randomness(),
                ),
            );
        });

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let mut reversion_info = cb.reversion_info_read(None);
        let was_warm = cb.query_bool();
        cb.account_access_list_write(
            tx_id.expr(),
            from_bytes::expr(&new_address.cells),
            1.expr(),
            was_warm.expr(),
            Some(&mut reversion_info),
        );

        let caller_address = cb.query_rlc();
        cb.call_context_lookup(
            0.expr(),
            None,
            CallContextFieldTag::CalleeAddress,
            from_bytes::expr(&caller_address.cells),
        );

        let nonce = RlpU64Gadget::construct(cb);
        cb.account_write(
            from_bytes::expr(&caller_address.cells),
            AccountFieldTag::Nonce,
            nonce.value() + 1.expr(),
            nonce.value(),
            Some(&mut reversion_info),
        );

        let mut callee_reversion_info = cb.reversion_info_write(Some(callee_call_id.expr()));
        cb.account_write(
            from_bytes::expr(&new_address.cells),
            AccountFieldTag::Nonce,
            1.expr(),
            0.expr(),
            Some(&mut callee_reversion_info),
        );

        let transfer = TransferGadget::construct(
            cb,
            from_bytes::expr(&caller_address.cells),
            from_bytes::expr(&new_address.cells),
            value.clone(),
            &mut callee_reversion_info,
        );

        let memory_expansion =
            MemoryExpansionGadget::construct(cb, [initialization_code.address()]);

        let stack_pointer_delta = 2.expr() + is_create2.expr();

        // EIP-150: all but one 64th of the caller's gas is sent to the callee.
        // let caller_gas_left =
        // (geth_step.gas.0 - geth_step.gas_cost.0 - memory_expansion_gas_cost) / 64;

        let initialization_code_word_size =
            ConstantDivisionGadget::construct(cb, initialization_code.length() + 31.expr(), 32);
        let keccak_gas_cost = GasCost::COPY_SHA3.expr()
            * is_create2.expr()
            * initialization_code_word_size.quotient();

        let gas_cost = GasCost::CREATE.expr() + memory_expansion.gas_cost() + keccak_gas_cost;
        let gas_remaining = cb.curr.state.gas_left.expr() - gas_cost;
        let gas_left = ConstantDivisionGadget::construct(cb, gas_remaining.clone(), 64);
        let callee_gas_left = gas_remaining - gas_left.quotient();
        for (field_tag, value) in [
            (
                CallContextFieldTag::ProgramCounter,
                cb.curr.state.program_counter.expr() + 1.expr(),
            ),
            (
                CallContextFieldTag::StackPointer,
                cb.curr.state.stack_pointer.expr() + stack_pointer_delta,
            ),
            (CallContextFieldTag::GasLeft, gas_left.quotient()),
            (
                CallContextFieldTag::MemorySize,
                memory_expansion.next_memory_word_size(),
            ),
            (
                CallContextFieldTag::ReversibleWriteCounter,
                cb.curr.state.reversible_write_counter.expr() + 2.expr(),
            ),
        ] {
            cb.call_context_lookup(true.expr(), None, field_tag, value);
        }

        for (field_tag, value) in [
            (CallContextFieldTag::CallerId, cb.curr.state.call_id.expr()),
            (CallContextFieldTag::IsSuccess, callee_is_success.expr()),
            (
                CallContextFieldTag::IsPersistent,
                callee_reversion_info.is_persistent(),
            ),
            (CallContextFieldTag::TxId, tx_id.expr()),
            (
                CallContextFieldTag::CallerAddress,
                from_bytes::expr(&caller_address.cells),
            ),
            (
                CallContextFieldTag::CalleeAddress,
                from_bytes::expr(&new_address.cells),
            ),
            (
                CallContextFieldTag::RwCounterEndOfReversion,
                callee_reversion_info.rw_counter_end_of_reversion(),
            ),
        ] {
            cb.call_context_lookup(true.expr(), Some(callee_call_id.expr()), field_tag, value);
        }

        cb.require_step_state_transition(StepStateTransition {
            rw_counter: Delta(cb.rw_counter_offset()),
            call_id: To(callee_call_id.expr()),
            is_root: To(false.expr()),
            is_create: To(true.expr()),
            code_hash: To(code_hash.expr()),
            gas_left: To(callee_gas_left),
            reversible_write_counter: To(3.expr()),
            ..StepStateTransition::new_context()
        });

        let keccak_input = cb.query_cell();
        let keccak_input_length = cb.query_cell();
        cb.condition(is_create2.expr(), |cb| {
            // TODO: some comments here explaining what's going on....
            // is the power of randomness in reverse order??? that seems impossible
            let randomness_raised_to_16 = cb.power_of_randomness()[15].clone();
            let randomness_raised_to_32 = randomness_raised_to_16.clone().square();
            let randomness_raised_to_64 = randomness_raised_to_32.clone().square();
            let randomness_raised_to_84 =
                randomness_raised_to_64.clone() * cb.power_of_randomness()[19].clone();
            cb.require_equal(
                "for CREATE2, keccak input is 0xff ++ address ++ salt ++ code_hash",
                keccak_input.expr(),
                0xff.expr() * randomness_raised_to_84
                    + caller_address.expr() * randomness_raised_to_64
                    + salt.expr() * randomness_raised_to_32
                    + code_hash.expr(),
            );
            cb.require_equal(
                "for CREATE2, keccak input length is 85",
                keccak_input_length.expr(),
                (1 + 20 + 32 + 32).expr(),
            );
        });

        cb.condition(not::expr(is_create2.expr()), |cb| {
            let randomness_raised_to_20 = cb.power_of_randomness()[19].clone();
            let randomness_raised_to_21 = cb.power_of_randomness()[20].clone();
            let randomness_raised_to_22 = cb.power_of_randomness()[21].clone();
            // let address_rlp_length = 21.expr();
            cb.require_equal(
                "for CREATE, keccak input is rlp([address, nonce])",
                keccak_input.expr(),
                nonce.rlp_rlc(cb)
                    + nonce.randomness_raised_to_rlp_length(cb)
                        * (((0xc0.expr() + 21.expr() + nonce.rlp_length())
                            * randomness_raised_to_21)
                            + (0x80 + 20).expr() * randomness_raised_to_20
                            + caller_address.expr()),
            );
            cb.require_equal(
                "for CREATE, keccak input length is rlp([address, nonce]).len()",
                keccak_input_length.expr(),
                (1 + 1 + 20).expr() + nonce.rlp_length(),
            );
        });

        let keccak_output = cb.query_word();
        cb.keccak_table_lookup(
            keccak_input.expr(),
            keccak_input_length.expr(),
            keccak_output.expr(),
        );

        cb.require_equal(
            "324124asfr",
            new_address.expr(),
            rlc::expr(
                &keccak_output.cells[..20]
                    .iter()
                    .map(Expr::expr)
                    .collect::<Vec<_>>(),
                cb.power_of_randomness(),
            ),
        );

        Self {
            opcode,
            is_create2,
            reversion_info,
            tx_id,
            was_warm,
            value,
            salt,
            new_address,
            caller_address,
            nonce,
            callee_reversion_info,
            transfer,
            initialization_code,
            memory_expansion,
            gas_left,
            callee_is_success,
            code_hash,
            keccak_output,
            keccak_input,
            keccak_input_length,
            initialization_code_word_size,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode.unwrap();
        let is_create2 = opcode == OpcodeId::CREATE2;
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
        self.is_create2.assign(
            region,
            offset,
            Value::known(is_create2.to_scalar().unwrap()),
        )?;

        let [value, initialization_code_start, initialization_code_length] = [0, 1, 2]
            .map(|i| step.rw_indices[i])
            .map(|idx| block.rws[idx].stack_value());
        let salt = if is_create2 {
            block.rws[step.rw_indices[3]].stack_value()
        } else {
            U256::zero()
        };

        let copy_rw_increase = initialization_code_length.as_usize();
        // dopy lookup here advances rw_counter by initialization_code_length;

        let values: Vec<_> = (4 + usize::from(is_create2)
            ..4 + usize::from(is_create2) + initialization_code_length.as_usize())
            .map(|i| block.rws[step.rw_indices[i]].memory_value())
            .collect();
        let mut code_hash = keccak256(&values);
        code_hash.reverse();
        let code_hash_rlc =
            RandomLinearCombination::random_linear_combine(code_hash.clone(), block.randomness);
        self.code_hash
            .assign(region, offset, Value::known(code_hash_rlc))?;

        let tx_access_rw =
            block.rws[step.rw_indices[7 + usize::from(is_create2) + copy_rw_increase]];

        let new_address = tx_access_rw.address().expect("asdfawefasdf");

        for (word, assignment) in [(&self.value, value), (&self.salt, salt)] {
            word.assign(region, offset, Some(assignment.to_le_bytes()))?;
        }
        let initialization_code_address = self.initialization_code.assign(
            region,
            offset,
            initialization_code_start,
            initialization_code_length,
            block.randomness,
        )?;

        let mut bytes = new_address.to_fixed_bytes();
        bytes.reverse();
        self.new_address.assign(region, offset, Some(bytes))?;

        self.tx_id
            .assign(region, offset, Value::known(tx.id.to_scalar().unwrap()))?;

        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;

        self.was_warm.assign(
            region,
            offset,
            Value::known(
                tx_access_rw
                    .tx_access_list_value_pair()
                    .1
                    .to_scalar()
                    .unwrap(),
            ),
        )?;

        let mut caller_address_bytes = call.callee_address.to_fixed_bytes();
        caller_address_bytes.reverse();
        self.caller_address
            .assign(region, offset, Some(caller_address_bytes.clone()))?;

        let caller_nonce = block.rws
            [step.rw_indices[9 + usize::from(is_create2) + copy_rw_increase]]
            .account_value_pair()
            .1
            .low_u64();
        self.nonce.assign(region, offset, caller_nonce)?;

        let [callee_rw_counter_end_of_reversion, callee_is_persistent] = [10, 11].map(|i| {
            block.rws[step.rw_indices[i + usize::from(is_create2) + copy_rw_increase]]
                .call_context_value()
        });

        self.callee_reversion_info.assign(
            region,
            offset,
            callee_rw_counter_end_of_reversion
                .low_u64()
                .try_into()
                .unwrap(),
            callee_is_persistent.low_u64() != 0,
        )?;

        let [caller_balance_pair, callee_balance_pair] = [13, 14].map(|i| {
            block.rws[step.rw_indices[i + usize::from(is_create2) + copy_rw_increase]]
                .account_value_pair()
        });
        self.transfer.assign(
            region,
            offset,
            caller_balance_pair,
            callee_balance_pair,
            value,
        )?;

        let (_next_memory_word_size, memory_expansion_gas_cost) = self.memory_expansion.assign(
            region,
            offset,
            step.memory_word_size(),
            [initialization_code_address],
        )?;

        let (initialization_code_word_size, _remainder) =
            self.initialization_code_word_size.assign(
                region,
                offset,
                (31u64 + initialization_code_length.as_u64()).into(),
            )?;

        self.gas_left.assign(
            region,
            offset,
            (step.gas_left
                - GasCost::CREATE.as_u64()
                - u64::try_from(memory_expansion_gas_cost).unwrap()
                - if is_create2 {
                    u64::try_from(initialization_code_word_size).unwrap()
                        * GasCost::COPY_SHA3.as_u64()
                } else {
                    0
                })
            .into(),
        )?;

        self.callee_is_success.assign(
            region,
            offset,
            Value::known(
                block.rws[step.rw_indices[21 + usize::from(is_create2) + copy_rw_increase]]
                    .call_context_value()
                    .to_scalar()
                    .unwrap(),
            ),
        )?;

        let keccak_input: Vec<u8> = if is_create2 {
            once(0xffu8)
                .chain(call.callee_address.to_fixed_bytes())
                .chain(salt.to_be_bytes())
                .chain(keccak256(&values))
                .collect()
        } else {
            let mut stream = rlp::RlpStream::new();
            stream.begin_list(2);
            stream.append(&call.callee_address);
            stream.append(&U256::from(caller_nonce));
            stream.out().to_vec()
        };
        let mut keccak_output = keccak256(&keccak_input);
        keccak_output.reverse();

        dbg!(keccak_input.clone());
        self.keccak_input.assign(
            region,
            offset,
            Value::known(rlc::value(keccak_input.iter().rev(), block.randomness)),
        )?;
        dbg!(keccak_input.len());
        self.keccak_input_length.assign(
            region,
            offset,
            Value::known(keccak_input.len().to_scalar().unwrap()),
        )?;
        self.keccak_output
            .assign(region, offset, Some(keccak_output))?;

        // let nonce_le_bytes = caller_nonce.to_le_bytes();
        // let most_significant_nonce_byte_index =
        //     (u64::from(u64::BITS + 1 - caller_nonce.leading_zeros()) + 7) / 8;
        // for i in 0..N_BYTES_U64 {
        //     self.most_significant_nonce_byte_selectors[i].assign(
        //         region,
        //         offset,
        //         Value::known(
        //             (u64::try_from(i).unwrap() == most_significant_nonce_byte_index)
        //                 .to_scalar()
        //                 .unwrap(),
        //         ),
        //     )?;
        // }

        Ok(())
    }
}

#[derive(Clone, Debug)]
struct RlpU64Gadget<F> {
    bytes: RandomLinearCombination<F, N_BYTES_U64>,
    is_most_significant_byte: [Cell<F>; N_BYTES_U64],
    most_significant_byte_is_zero: IsZeroGadget<F>,
    is_less_than_128: Cell<F>,
}

impl<F: Field> RlpU64Gadget<F> {
    fn construct(cb: &mut ConstraintBuilder<F>) -> Self {
        let bytes = cb.query_rlc();
        let is_most_significant_byte = [(); N_BYTES_U64].map(|()| cb.query_bool());
        let most_significant_byte = sum::expr(
            bytes
                .cells
                .iter()
                .zip(&is_most_significant_byte)
                .map(|(byte, indicator)| byte.expr() * indicator.expr()),
        );
        let most_significant_byte_is_zero = IsZeroGadget::construct(cb, most_significant_byte);
        let is_less_than_128 = cb.query_bool();

        cb.require_boolean(
            "at most one of is_most_significant_byte is one",
            sum::expr(&is_most_significant_byte),
        );

        let value = from_bytes::expr(&bytes.cells);
        cb.condition(most_significant_byte_is_zero.expr(), |cb| {
            cb.require_zero("if most significant byte is 0, value is 0", value.clone());
        });
        for i in 0..N_BYTES_U64 {
            cb.condition(is_most_significant_byte[i].expr(), |cb| {
                cb.require_equal(
                    "most significant byte is non-zero",
                    most_significant_byte_is_zero.expr(),
                    0.expr(),
                );
                cb.require_equal(
                    "higher bytes are 0",
                    from_bytes::expr(&bytes.cells[..i + 1]),
                    value.clone(),
                );
            });
        }

        cb.condition(is_less_than_128.expr(), |cb| {
            cb.range_lookup(value, 128);
        });

        Self {
            bytes,
            is_most_significant_byte,
            most_significant_byte_is_zero,
            is_less_than_128,
        }
    }

    fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: u64,
    ) -> Result<(), Error> {
        // dbg!(value);

        let bytes = value.to_le_bytes();
        // dbg!(bytes.clone());
        let most_significant_byte_index = bytes
            .iter()
            .rev()
            .position(|byte| *byte != 0)
            .map(|i| N_BYTES_U64 - i - 1);
        // dbg!(most_significant_byte_index);
        self.most_significant_byte_is_zero.assign(
            region,
            offset,
            most_significant_byte_index
                .map(|i| u64::from(bytes[i]).into())
                .unwrap_or(F::zero()),
        )?;
        self.bytes.assign(region, offset, Some(bytes))?;
        for i in 0..N_BYTES_U64 {
            self.is_most_significant_byte[i].assign(
                region,
                offset,
                Value::known(
                    (Some(i) == most_significant_byte_index)
                        .to_scalar()
                        .unwrap(),
                ),
            )?;
        }
        self.is_less_than_128.assign(
            region,
            offset,
            Value::known((value < 128).to_scalar().unwrap()),
        )?;
        Ok(())
    }

    fn value(&self) -> Expression<F> {
        from_bytes::expr(&self.bytes.cells)
    }

    fn n_bytes_nonce(&self) -> Expression<F> {
        sum::expr(
            self.is_most_significant_byte
                .iter()
                .enumerate()
                .map(|(i, indicator)| (1 + i).expr() * indicator.expr()),
        )
    }

    fn rlp_length(&self) -> Expression<F> {
        1.expr() + not::expr(self.is_less_than_128.expr()) * self.n_bytes_nonce()
    }

    fn rlp_rlc(&self, cb: &ConstraintBuilder<F>) -> Expression<F> {
        select::expr(
            and::expr(&[
                self.is_less_than_128.expr(),
                not::expr(self.most_significant_byte_is_zero.expr()),
            ]),
            self.value(),
            (0x80.expr() + self.n_bytes_nonce()) * self.randomness_raised_n_bytes_nonce(cb)
                + self.bytes.expr(),
        )
    }

    fn randomness_raised_to_rlp_length(&self, cb: &ConstraintBuilder<F>) -> Expression<F> {
        let powers_of_randomness = cb.power_of_randomness();
        powers_of_randomness[0].clone()
            * select::expr(
                self.is_less_than_128.expr(),
                1.expr(),
                self.randomness_raised_n_bytes_nonce(cb),
            )
    }

    fn randomness_raised_n_bytes_nonce(&self, cb: &ConstraintBuilder<F>) -> Expression<F> {
        let powers_of_randomness = cb.power_of_randomness();
        select::expr(
            self.most_significant_byte_is_zero.expr(),
            1.expr(),
            sum::expr(
                self.is_most_significant_byte
                    .iter()
                    .zip(powers_of_randomness)
                    .map(|(indicator, power)| indicator.expr() * power.clone()),
            ),
        )
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::run_test_circuits;
    use eth_types::{
        address, bytecode, evm_types::OpcodeId, geth_types::Account, Address, Bytecode, ToWord,
        Word,
    };
    use ethers_core::utils::rlp;
    use itertools::Itertools;
    use lazy_static::lazy_static;
    use mock::{eth, TestContext};

    const CALLEE_ADDRESS: Address = Address::repeat_byte(0xff);
    lazy_static! {
        static ref CALLER_ADDRESS: Address = address!("0x00bbccddee000000000000000000000000002400");
    }

    fn callee_bytecode(is_return: bool, offset: u64, length: u64) -> Bytecode {
        let memory_bytes = [0x60; 10];
        let memory_address = 0;
        let memory_value = Word::from_big_endian(&memory_bytes);
        let mut code = bytecode! {
            PUSH10(memory_value)
            PUSH1(memory_address)
            MSTORE
            PUSH2(length)
            PUSH2(32u64 - u64::try_from(memory_bytes.len()).unwrap() + offset)
        };
        code.write_op(if is_return {
            OpcodeId::RETURN
        } else {
            OpcodeId::REVERT
        });
        code
    }

    fn caller_bytecode(return_data_offset: u64, return_data_length: u64) -> Bytecode {
        bytecode! {
            PUSH32(return_data_length)
            PUSH32(return_data_offset)
            PUSH32(0) // call data length
            PUSH32(0) // call data offset
            PUSH32(0) // value
            PUSH32(CALLEE_ADDRESS.to_word())
            PUSH32(4000) // gas
            CALL
            STOP
        }
    }

    #[test]
    fn mason2() {
        let test_parameters = [(0, 0), (0, 10), (300, 20), (1000, 0)];
        for ((offset, length), is_return) in test_parameters.iter().cartesian_product(&[true])
        // FIX MEEEEEE there's an issue when the init call reverts.
        {
            let initializer = callee_bytecode(*is_return, *offset, *length).code();

            let root_code = bytecode! {
                PUSH32(Word::from_big_endian(&initializer))
                PUSH1(0)
                MSTORE

                PUSH1(45)                       // salt
                PUSH1(initializer.len())        // size
                PUSH1(32 - initializer.len())   // offset
                PUSH1(0)                        // value

                CREATE2
            };

            let caller = Account {
                address: *CALLER_ADDRESS,
                code: root_code.into(),
                nonce: Word::one(),
                balance: eth(10),
                ..Default::default()
            };

            let test_context = TestContext::<2, 1>::new(
                None,
                |accs| {
                    accs[0]
                        .address(address!("0x000000000000000000000000000000000000cafe"))
                        .balance(eth(10));
                    accs[1].account(&caller);
                },
                |mut txs, accs| {
                    txs[0]
                        .from(accs[0].address)
                        .to(accs[1].address)
                        .gas(100000u64.into());
                },
                |block, _| block,
            )
            .unwrap();

            assert_eq!(
                run_test_circuits(test_context, None),
                Ok(()),
                "(offset, length, is_return) = {:?}",
                (*offset, *length, *is_return),
            );
        }
    }

    #[test]
    fn test_create2() {
        let test_parameters = [(0, 0), (0, 10), (300, 20), (1000, 0)];
        for ((offset, length), is_return) in test_parameters.iter().cartesian_product(&[true]) {
            let initializer = callee_bytecode(*is_return, *offset, *length).code();

            let root_code = bytecode! {
                PUSH32(Word::from_big_endian(&initializer))
                PUSH1(0)
                MSTORE

                PUSH1(34)                       // salt
                PUSH1(initializer.len())        // size
                PUSH1(32 - initializer.len())   // offset
                PUSH1(12)                       // value

                CREATE2
            };

            let caller = Account {
                address: *CALLER_ADDRESS,
                code: root_code.into(),
                nonce: Word::one(),
                balance: eth(10),
                ..Default::default()
            };

            let test_context = TestContext::<2, 1>::new(
                None,
                |accs| {
                    accs[0]
                        .address(address!("0x000000000000000000000000000000000000cafe"))
                        .balance(eth(10));
                    accs[1].account(&caller);
                },
                |mut txs, accs| {
                    txs[0]
                        .from(accs[0].address)
                        .to(accs[1].address)
                        .gas(100000u64.into());
                },
                |block, _| block,
            )
            .unwrap();

            assert_eq!(
                run_test_circuits(test_context, None),
                Ok(()),
                "(offset, length, is_return) = {:?}",
                (*offset, *length, *is_return),
            );
        }
    }

    #[test]
    fn mason() {
        // Test the case where the initialization call is successful, but the CREATE
        // call is reverted.
        let initializer = callee_bytecode(true, 0, 10).code();

        let root_code = bytecode! {
            PUSH32(Word::from_big_endian(&initializer))
            PUSH1(0)
            MSTORE

            PUSH1(initializer.len())        // size
            PUSH1(32 - initializer.len())   // offset
            PUSH1(0)                        // value

            CREATE
            PUSH1(0)
            PUSH1(0)
            REVERT
        };

        let caller = Account {
            address: *CALLER_ADDRESS,
            code: root_code.into(),
            nonce: Word::one(),
            balance: eth(10),
            ..Default::default()
        };

        let test_context = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(eth(10));
                accs[1].account(&caller);
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[0].address)
                    .to(accs[1].address)
                    .gas(100000u64.into());
            },
            |block, _| block,
        )
        .unwrap();

        assert_eq!(run_test_circuits(test_context, None), Ok(()),);
    }

    #[test]
    fn create() {
        // Test the case where the initialization call is successful, but the CREATE
        // call is reverted.
        let initializer = callee_bytecode(true, 0, 10).code();

        let root_code = bytecode! {
            PUSH32(Word::from_big_endian(&initializer))
            PUSH1(0)
            MSTORE

            PUSH1(initializer.len())        // size
            PUSH1(32 - initializer.len())   // offset
            PUSH1(0)                        // value

            CREATE
            PUSH1(0)
            PUSH1(0)
            REVERT
        };

        let caller = Account {
            address: *CALLER_ADDRESS,
            code: root_code.into(),
            nonce: Word::one(),
            balance: eth(10),
            ..Default::default()
        };

        let test_context = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(eth(10));
                accs[1].account(&caller);
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[0].address)
                    .to(accs[1].address)
                    .gas(100000u64.into());
            },
            |block, _| block,
        )
        .unwrap();

        assert_eq!(run_test_circuits(test_context, None), Ok(()),);
    }

    #[test]
    fn create2() {
        // Test the case where the initialization call is successful, but the CREATE
        // call is reverted.
        let initializer = callee_bytecode(true, 0, 10).code();

        let root_code = bytecode! {
            PUSH32(Word::from_big_endian(&initializer))
            PUSH1(0)
            MSTORE

            PUSH1(initializer.len())        // size
            PUSH1(32 - initializer.len())   // offset
            PUSH1(0)                        // value
            PUSH1(56)                       // salt

            CREATE2
        };

        let caller = Account {
            address: *CALLER_ADDRESS,
            code: root_code.into(),
            nonce: Word::one(),
            balance: eth(10),
            ..Default::default()
        };

        let test_context = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(eth(10));
                accs[1].account(&caller);
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[0].address)
                    .to(accs[1].address)
                    .gas(100000u64.into());
            },
            |block, _| block,
        )
        .unwrap();

        assert_eq!(run_test_circuits(test_context, None), Ok(()),);
    }

    #[test]
    fn create2_really_create() {
        for nonce in [1, 0, 1, 0xff, 0x100, 0x1000000] {
            dbg!(nonce);
            let initializer = callee_bytecode(true, 0, 10).code();

            let root_code = bytecode! {
                PUSH32(Word::from_big_endian(&initializer))
                PUSH1(0)
                MSTORE

                PUSH1(initializer.len())        // size
                PUSH1(32 - initializer.len())   // offset
                PUSH1(0)                        // value

                CREATE
            };

            let caller = Account {
                address: *CALLER_ADDRESS,
                code: root_code.into(),
                nonce: nonce.into(),
                balance: eth(10),
                ..Default::default()
            };

            let test_context = TestContext::<2, 1>::new(
                None,
                |accs| {
                    accs[0]
                        .address(address!("0x000000000000000000000000000000000000cafe"))
                        .balance(eth(10));
                    accs[1].account(&caller);
                },
                |mut txs, accs| {
                    txs[0]
                        .from(accs[0].address)
                        .to(accs[1].address)
                        .gas(100000u64.into());
                },
                |block, _| block,
            )
            .unwrap();

            assert_eq!(
                run_test_circuits(test_context, None),
                Ok(()),
                "nonce = {}",
                nonce
            );
        }
    }
}
