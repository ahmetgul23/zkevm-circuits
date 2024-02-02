use super::CachedRegion;
use crate::{
    evm_circuit::util::{
        and,
        constraint_builder::EVMConstraintBuilder,
        math_gadget::{IsEqualGadget, IsZeroWordGadget},
        select,
    },
    table::AccountFieldTag,
    util::{
        word::{Word, WordCell, WordExpr},
        Expr,
    },
};
use eth_types::{geth_types::TxType, Field, U256};
use halo2_proofs::plonk::{Error, Expression};

/// L1 Msg Transaction gadget for some extra handling
#[derive(Clone, Debug)]
pub(crate) struct TxL1MsgGadget<F> {
    /// tx is l1 msg tx
    tx_is_l1msg: IsEqualGadget<F>,
    /// caller is empty
    is_caller_empty: IsZeroWordGadget<F, WordCell<F>>,
    //caller_codehash: Cell<F>,
    caller_codehash: WordCell<F>,
}

impl<F: Field> TxL1MsgGadget<F> {
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        tx_type: Expression<F>,
        caller_address: Word<Expression<F>>,
    ) -> Self {
        let tx_is_l1msg =
            IsEqualGadget::construct(cb, tx_type.expr(), (TxType::L1Msg as u64).expr());
        let caller_codehash = cb.query_word_unchecked();
        let is_caller_empty = cb.annotation("is caller address not existed", |cb| {
            IsZeroWordGadget::construct(cb, &caller_codehash)
        });

        cb.condition(tx_is_l1msg.expr(), |cb| {
            cb.account_read(
                caller_address.clone(),
                AccountFieldTag::CodeHash,
                caller_codehash.to_word(),
            );
        });

        cb.condition(
            and::expr([tx_is_l1msg.expr(), is_caller_empty.expr()]),
            |cb| {
                cb.account_write(
                    caller_address.to_word(),
                    AccountFieldTag::CodeHash,
                    cb.empty_code_hash(),
                    Word::zero(),
                    None,
                );
                #[cfg(feature = "scroll")]
                cb.account_write(
                    caller_address.to_word(),
                    AccountFieldTag::KeccakCodeHash,
                    //cb.empty_keccak_hash_rlc(),
                    cb.empty_code_hash(),
                    Word::zero(),
                    None,
                );
            },
        );

        Self {
            tx_is_l1msg,
            caller_codehash,
            is_caller_empty,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        tx_type: TxType,
        code_hash: U256,
    ) -> Result<(), Error> {
        self.tx_is_l1msg.assign(
            region,
            offset,
            F::from(tx_type as u64),
            F::from(TxType::L1Msg as u64),
        )?;

        self.caller_codehash
            .assign_u256(region, offset, code_hash)?;
        self.is_caller_empty
            .assign_u256(region, offset, code_hash)?;

        Ok(())
    }

    // return rw_delta WHEN tx is l1msg
    pub(crate) fn rw_delta(&self) -> Expression<F> {
        select::expr(
            self.is_caller_empty.expr(),
            if cfg!(feature = "scroll") {
                3.expr()
            } else {
                2.expr()
            },
            1.expr(),
        )
    }

    pub(crate) fn is_l1_msg(&self) -> Expression<F> {
        self.tx_is_l1msg.expr()
    }
}
