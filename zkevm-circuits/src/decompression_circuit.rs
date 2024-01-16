//! This circuit decodes zstd compressed data.

use std::marker::PhantomData;

use array_init::array_init;
use eth_types::Field;
use gadgets::util::{and, not, Expr};
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, SecondPhase},
    poly::Rotation,
};

use crate::{
    evm_circuit::util::constraint_builder::{BaseConstraintBuilder, ConstrainBuilderCommon},
    table::U8Table,
    util::{Challenges, SubCircuit, SubCircuitConfig},
    witness::{Block, N_BITS_PER_BYTE},
};

/// Tables, challenge API used to configure the Decompression circuit.
pub struct DecompressionCircuitConfigArgs<F> {
    /// Challenge API.
    pub challenges: Challenges<Expression<F>>,
    /// U8 table, i.e. RangeTable for 0..8.
    pub u8_table: U8Table,
}

/// The Decompression circuit's configuration. The columns used to constrain the Decompression
/// logic are defined here. Refer the [design doc][doclink] for design decisions and specifications.
///
/// [doclink]: https://www.notion.so/scrollzkp/zstd-in-circuit-decompression-23f8036538e440ebbbc17c69033d36f5?pvs=4
#[derive(Clone, Debug)]
pub struct DecompressionCircuitConfig<F> {
    /// Fixed column to mark all enabled rows.
    q_enable: Column<Fixed>,
    /// Fixed column to mark the first row in the layout.
    q_first: Column<Fixed>,
    /// Boolean column to mark whether or not the row represents a padding column.
    is_padding: Column<Advice>,

    /// The index of the byte being processed within the current frame. The first byte has a
    /// byte_idx == 1. byte_idx follows the relation byte_idx' >= byte_idx. That is, byte_idx is
    /// increasing, but can repeat over two or more rows if we are decoding bits from the same byte
    /// over those consecutive rows. For instance, if a Huffman Code bitstring is 2 bits long,
    /// we might end up decoding on the same byte_idx at the most 4 times.
    byte_idx: Column<Advice>,
    /// The number of bytes in the zstd encoded data.
    encoded_len: Column<Advice>,
    /// The byte value at the current byte index. This will be decomposed in its bits.
    value_byte: Column<Advice>,
    /// The 8 bits for the above byte, little-endian.
    value_bits: [Column<Advice>; N_BITS_PER_BYTE],
    /// The random linear combination of all encoded bytes up to and including the current one.
    value_rlc: Column<Advice>,
    /// An accumulator for the number of decoded bytes. For every byte decoded, we expect the
    /// accumulator to be incremented.
    decoded_len: Column<Advice>,
    /// The byte value that is decoded at the current row. We don't decode a byte at every row. And
    /// we might end up decoding more than one bytes while the byte_idx remains the same, for
    /// instance, while processing bits and decoding the Huffman Codes.
    decoded_byte: Column<Advice>,
    /// The random linear combination of all decoded bytes up to and including the current one.
    decoded_rlc: Column<Advice>,

    _data: PhantomData<F>,
}

impl<F: Field> SubCircuitConfig<F> for DecompressionCircuitConfig<F> {
    type ConfigArgs = DecompressionCircuitConfigArgs<F>;

    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            challenges: _,
            u8_table,
        }: Self::ConfigArgs,
    ) -> Self {
        let q_enable = meta.fixed_column();
        let q_first = meta.fixed_column();
        let is_padding = meta.advice_column();
        let byte_idx = meta.advice_column();
        let encoded_len = meta.advice_column();
        let value_byte = meta.advice_column();
        let value_bits = array_init(|_| meta.advice_column());
        let value_rlc = meta.advice_column_in(SecondPhase);
        let decoded_len = meta.advice_column();
        let decoded_byte = meta.advice_column();
        let decoded_rlc = meta.advice_column_in(SecondPhase);

        meta.create_gate("DecompressionCircuit: all rows", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_boolean(
                "is_padding is boolean",
                meta.query_advice(is_padding, Rotation::cur()),
            );

            cb.require_boolean(
                "is_padding transitions from 0 -> 1 only once",
                meta.query_advice(is_padding, Rotation::next())
                    - meta.query_advice(is_padding, Rotation::cur()),
            );

            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        meta.create_gate("DecompressionCircuit: all non-padded rows", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            let bits = value_bits.map(|bit| meta.query_advice(bit, Rotation::cur()));

            // This is also sufficient to check that value_byte is in 0..=255
            cb.require_equal(
                "verify value byte's bits decomposition",
                meta.query_advice(value_byte, Rotation::cur()),
                bits[0].expr()
                    + 2.expr() * bits[1].expr()
                    + 4.expr() * bits[2].expr()
                    + 8.expr() * bits[3].expr()
                    + 16.expr() * bits[4].expr()
                    + 32.expr() * bits[5].expr()
                    + 64.expr() * bits[6].expr()
                    + 128.expr() * bits[7].expr(),
            );
            for bit in bits {
                cb.require_boolean("every value bit is boolean", bit.expr());
            }

            cb.require_equal(
                "encoded length remains the same",
                meta.query_advice(encoded_len, Rotation::cur()),
                meta.query_advice(encoded_len, Rotation::next()),
            );

            cb.gate(and::expr([
                meta.query_fixed(q_enable, Rotation::cur()),
                not::expr(meta.query_advice(is_padding, Rotation::cur())),
            ]))
        });

        meta.lookup(
            "DecompressionCircuit: decoded byte is in U8 range",
            |meta| {
                let condition = and::expr([
                    meta.query_fixed(q_enable, Rotation::cur()),
                    not::expr(meta.query_advice(is_padding, Rotation::cur())),
                ]);

                vec![(
                    condition * meta.query_advice(decoded_byte, Rotation::cur()),
                    u8_table.into(),
                )]
            },
        );

        meta.create_gate("DecompressionCircuit: first row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "value_rlc == value_byte",
                meta.query_advice(value_rlc, Rotation::cur()),
                meta.query_advice(value_byte, Rotation::cur()),
            );

            cb.require_equal(
                "byte_idx == 1",
                meta.query_advice(byte_idx, Rotation::cur()),
                1.expr(),
            );

            cb.gate(and::expr([
                meta.query_fixed(q_enable, Rotation::cur()),
                meta.query_fixed(q_first, Rotation::cur()),
                not::expr(meta.query_advice(is_padding, Rotation::cur())),
            ]))
        });

        meta.create_gate("DecompressionCircuit: last row", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            cb.require_equal(
                "byte_idx == encoded_len",
                meta.query_advice(byte_idx, Rotation::cur()),
                meta.query_advice(encoded_len, Rotation::cur()),
            );

            cb.gate(and::expr([
                meta.query_fixed(q_enable, Rotation::cur()),
                meta.query_advice(is_padding, Rotation::next())
                    - meta.query_advice(is_padding, Rotation::cur()),
            ]))
        });

        Self {
            q_enable,
            q_first,
            is_padding,
            byte_idx,
            encoded_len,
            value_byte,
            value_bits,
            value_rlc,
            decoded_len,
            decoded_byte,
            decoded_rlc,
            _data: PhantomData,
        }
    }
}

/// The Decompression circuit decodes an instance of zstd compressed data.
#[derive(Clone, Debug)]
pub struct DecompressionCircuit<F> {
    _data: PhantomData<F>,
}

impl<F: Field> SubCircuit<F> for DecompressionCircuit<F> {
    type Config = DecompressionCircuitConfig<F>;

    fn new_from_block(_block: &Block<F>) -> Self {
        unimplemented!()
    }

    fn min_num_rows_block(_block: &Block<F>) -> (usize, usize) {
        unimplemented!()
    }

    fn synthesize_sub(
        &self,
        _config: &Self::Config,
        _challenges: &Challenges<Value<F>>,
        _layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        unimplemented!()
    }
}
