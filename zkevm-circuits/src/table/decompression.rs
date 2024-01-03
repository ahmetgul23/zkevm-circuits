use array_init::array_init;
use eth_types::Field;
use gadgets::binary_number::{BinaryNumberChip, BinaryNumberConfig};
use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Fixed},
    poly::Rotation,
};

use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, witness::FseSymbol};

use super::LookupTable;

/// Maximum number of symbols (weights), i.e. symbol in [0, N_MAX_SYMBOLS).
pub const N_MAX_SYMBOLS: usize = 8;

/// Number of bits used to represent the symbol in binary form. This will be used as a helper
/// gadget to form equality constraints over the symbol's value.
pub const N_BITS_SYMBOL: usize = 3;

/// The finite state entropy table in its default view, i.e. when the ``state`` increments.
///
/// | State | Symbol | Baseline | Nb  |
/// |-------|--------|----------|-----|
/// | 0x00  | s0     | 0x04     | 1   |
/// | 0x01  | s0     | 0x06     | 1   |
/// | 0x02  | s0     | 0x08     | 1   |
/// | ...   | ...    | ...      | ... |
/// | 0x1d  | s0     | 0x03     | 0   |
/// | 0x1e  | s1     | 0x0c     | 2   |
/// | 0x1f  | s2     | 0x10     | 4   |
///
/// An example for FseTable with AL (accuracy log) 5, i.e. 1 << 5 states is demonstrated above. For
/// more details, refer the [zstd worked example][doclink]
///
/// [doclink]: https://nigeltao.github.io/blog/2022/zstandard-part-5-fse.html#state-machine
#[derive(Clone, Debug)]
pub struct FseTable {
    /// Fixed column to denote whether the constraints will be enabled or not.
    pub q_enabled: Column<Fixed>,
    /// The encoded/decoded data's instance ID where this FSE table belongs.
    pub instance_idx: Column<Advice>,
    /// The frame's ID within the data instance where this FSE table belongs.
    pub frame_idx: Column<Advice>,
    /// The byte offset within the data instance where the encoded FSE table begins. This is
    /// 1-indexed, i.e. byte_offset == 1 at the first byte.
    pub byte_offset: Column<Advice>,
    /// The size of the FSE table that starts at byte_offset.
    pub table_size: Column<Advice>,
    /// Incremental index for this specific FSE table.
    pub idx: Column<Advice>,
    /// Incremental state that starts at 0x00 and increments by 1 until it reaches table_size - 1
    /// at the final row.
    pub state: Column<Advice>,
    /// Denotes the weight from the canonical Huffman code representation of the Huffman code. This
    /// is also the symbol emitted from the FSE table at this row's state.
    pub symbol: Column<Advice>,
    /// The binary representation of the symbol value.
    pub symbol_bits: BinaryNumberConfig<FseSymbol, N_BITS_SYMBOL>,
    /// Denotes the baseline field.
    pub baseline: Column<Advice>,
    /// The last seen baseline fields by symbol.
    pub last_baselines: [Column<Advice>; N_MAX_SYMBOLS],
    /// The number of bits to be read from bitstream at this state.
    pub nb: Column<Advice>,
    /// The smaller power of two assigned to this state. The following must hold:
    /// - 2 ^ nb == SPoT.
    pub spot: Column<Advice>,
    /// The last seen SPoT at a state.
    pub last_spots: [Column<Advice>; N_MAX_SYMBOLS],
    /// An accumulator over SPoTs values.
    pub spot_accs: [Column<Advice>; N_MAX_SYMBOLS],
}

impl FseTable {
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enabled = meta.fixed_column();
        let symbol = meta.advice_column();
        let fse_table = Self {
            q_enabled,
            instance_idx: meta.advice_column(),
            frame_idx: meta.advice_column(),
            byte_offset: meta.advice_column(),
            table_size: meta.advice_column(),
            idx: meta.advice_column(),
            state: meta.advice_column(),
            symbol,
            symbol_bits: BinaryNumberChip::configure(meta, q_enabled, Some(symbol.into())),
            baseline: meta.advice_column(),
            last_baselines: array_init(|_| meta.advice_column()),
            nb: meta.advice_column(),
            spot: meta.advice_column(),
            last_spots: array_init(|_| meta.advice_column()),
            spot_accs: array_init(|_| meta.advice_column()),
        };

        meta.create_gate("TODO", |meta| {
            let mut cb = BaseConstraintBuilder::default();
            cb.gate(meta.query_fixed(q_enabled, Rotation::cur()))
        });

        fse_table
    }
}

impl<F: Field> LookupTable<F> for FseTable {
    fn columns(&self) -> Vec<halo2_proofs::plonk::Column<halo2_proofs::plonk::Any>> {
        unimplemented!()
    }

    fn annotations(&self) -> Vec<String> {
        unimplemented!()
    }
}

/// An auxiliary table used to ensure that the FSE table was reconstructed appropriately. Contrary
/// to the FseTable where the state is incremental, in the Auxiliary table we club together rows by
/// symbol. Which means, we will have rows with symbol s0 (and varying, but not necessarily
/// incremental states) clubbed together, followed by symbol s1 and so on.
///
/// | State | Symbol | Baseline | Nb  |
/// |-------|--------|----------|-----|
/// | 0x00  | s0     | ...      | ... |
/// | 0x01  | s0     | ...      | ... |
/// | 0x02  | s0     | ...      | ... |
/// | 0x03  | s1     | ...      | ... |
/// | 0x0c  | s1     | ...      | ... |
/// | 0x11  | s1     | ...      | ... |
/// | 0x15  | s1     | ...      | ... |
/// | 0x1a  | s1     | ...      | ... |
/// | 0x1e  | s1     | ...      | ... |
/// | ...   | ...    | ...      | ... |
/// | 0x09  | s6     | ...      | ... |
///
/// Above is a representation of this table. Primarily we are interested in verifying that:
/// - next state (for the same symbol) was assigned correctly
/// - the number of times this symbol appears is assigned correctly
///
/// For more details, refer the [FSE reconstruction][doclink] section.
///
/// [doclink]: https://nigeltao.github.io/blog/2022/zstandard-part-5-fse.html#fse-reconstruction
#[derive(Clone, Debug)]
pub struct FseAuxiliaryTable {
    /// Fixed column to denote whether the constraints will be enabled or not.
    pub q_enabled: Column<Fixed>,
    /// The encoded/decoded data's instance ID where this FSE table belongs.
    pub instance_idx: Column<Advice>,
    /// The frame's ID within the data instance where this FSE table belongs.
    pub frame_idx: Column<Advice>,
    /// The byte offset within the data instance where the encoded FSE table begins. This is
    /// 1-indexed, i.e. byte_offset == 1 at the first byte.
    pub byte_offset: Column<Advice>,
    /// The size of the FSE table that starts at byte_offset.
    pub table_size: Column<Advice>,
    /// Helper column for (table_size >> 1).
    pub table_size_rs_1: Column<Advice>,
    /// Helper column for (table_size >> 3).
    pub table_size_rs_3: Column<Advice>,
    /// Incremental index.
    pub idx: Column<Advice>,
    /// The symbol (weight) assigned to this state.
    pub symbol: Column<Advice>,
    /// Represents the number of times this symbol appears in the FSE table. This value does not
    /// change while the symbol in the table remains the same.
    pub symbol_count: Column<Advice>,
    /// An accumulator that resets to 1 each time we encounter a new symbol in the Auxiliary table
    /// and increments by 1 while the symbol remains the same. On the row where symbol' != symbol
    /// we have: symbol_count == symbol_count_acc.
    pub symbol_count_acc: Column<Advice>,
    /// The state in FSE. In the Auxiliary table, it does not increment by 1. Instead, it follows:
    /// - state'' == state   + table_size_rs_1 + table_size_rs_3 + 3
    /// - state'  == state'' & (table_size - 1)
    ///
    /// where state' is the next row's state.
    pub state: Column<Advice>,
}

impl FseAuxiliaryTable {
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enabled = meta.fixed_column();
        let aux_table = Self {
            q_enabled,
            instance_idx: meta.advice_column(),
            frame_idx: meta.advice_column(),
            byte_offset: meta.advice_column(),
            table_size: meta.advice_column(),
            table_size_rs_1: meta.advice_column(),
            table_size_rs_3: meta.advice_column(),
            idx: meta.advice_column(),
            symbol: meta.advice_column(),
            symbol_count: meta.advice_column(),
            symbol_count_acc: meta.advice_column(),
            state: meta.advice_column(),
        };

        meta.create_gate("TODO", |meta| {
            let mut cb = BaseConstraintBuilder::default();
            cb.gate(meta.query_fixed(q_enabled, Rotation::cur()))
        });

        aux_table
    }
}

impl<F: Field> LookupTable<F> for FseAuxiliaryTable {
    fn columns(&self) -> Vec<halo2_proofs::plonk::Column<halo2_proofs::plonk::Any>> {
        unimplemented!()
    }

    fn annotations(&self) -> Vec<String> {
        unimplemented!()
    }
}

/// The Huffman codes table maps the canonical weights (symbols as per FseTable) to the Huffman
/// codes.
#[derive(Clone, Debug)]
pub struct HuffmanCodesTable {
    /// Fixed column to denote whether the constraints will be enabled or not.
    pub q_enabled: Column<Fixed>,
    /// The encoded/decoded data's instance ID where this FSE table belongs.
    pub instance_idx: Column<Advice>,
    /// The frame's ID within the data instance where this FSE table belongs.
    pub frame_idx: Column<Advice>,
    /// The byte offset within the data instance where the encoded FSE table begins. This is
    /// 1-indexed, i.e. byte_offset == 1 at the first byte.
    pub byte_offset: Column<Advice>,
    /// The byte that is being encoded by a Huffman code.
    pub symbol: Column<Advice>,
    /// The weight assigned to this symbol as per the canonical Huffman code weights.
    pub weight: Column<Advice>,
    /// A binary representation of the weight's value.
    pub weight_bits: BinaryNumberConfig<FseSymbol, N_BITS_SYMBOL>,
    /// An accumulator over the weight values.
    pub weight_acc: Column<Advice>,
    /// Helper column to denote 2 ^ (weight - 1).
    pub pow2_weight: Column<Advice>,
    /// The sum of canonical Huffman code weights. This value does not change over the rows for a
    /// specific Huffman code, i.e. as long as the tuple (instance_idx, frame_idx, byte_offset) is
    /// the same.
    pub sum_weights: Column<Advice>,
    /// The maximum length of a bitstring as per this Huffman code. Again, this value does not
    /// change over the rows for a specific Huffman code.
    pub max_bitstring_len: Column<Advice>,
    /// The length of the bitstring encoding this symbol in the Huffman code.
    pub bitstring_len: Column<Advice>,
    /// As per Huffman coding, every symbol is mapped to a bit value, which is then represented in
    /// binary form (padded) of length bitstring_len.
    pub bit_value: Column<Advice>,
    /// The last seen bit_value for each symbol in this Huffman coding.
    pub last_bit_values: [Column<Advice>; N_MAX_SYMBOLS],
}

impl HuffmanCodesTable {
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enabled = meta.fixed_column();
        let weight = meta.advice_column();
        let huffman_table = Self {
            q_enabled,
            instance_idx: meta.advice_column(),
            frame_idx: meta.advice_column(),
            byte_offset: meta.advice_column(),
            symbol: meta.advice_column(),
            weight,
            weight_bits: BinaryNumberChip::configure(meta, q_enabled, Some(weight.into())),
            pow2_weight: meta.advice_column(),
            weight_acc: meta.advice_column(),
            sum_weights: meta.advice_column(),
            max_bitstring_len: meta.advice_column(),
            bitstring_len: meta.advice_column(),
            bit_value: meta.advice_column(),
            last_bit_values: array_init(|_| meta.advice_column()),
        };

        meta.create_gate("TODO", |meta| {
            let mut cb = BaseConstraintBuilder::default();
            cb.gate(meta.query_fixed(q_enabled, Rotation::cur()))
        });

        huffman_table
    }
}

impl<F: Field> LookupTable<F> for HuffmanCodesTable {
    fn columns(&self) -> Vec<halo2_proofs::plonk::Column<halo2_proofs::plonk::Any>> {
        unimplemented!()
    }

    fn annotations(&self) -> Vec<String> {
        unimplemented!()
    }
}

/// An auxiliary table for the Huffman Codes. In Huffman coding a symbol (byte) is mapped to a
/// bitstring of particular length such that more frequently occuring symbols are mapped to
/// bitstrings of smaller lengths.
///
/// We already have the symbols and their bit_value in the HuffmanCodesTable. However, we still
/// need to validate that the bit_value is in fact assigned correctly. Since bitstrings may not be
/// byte-aligned, i.e. a bitstring can span over 2 bytes (assuming a maximum bitstring length of 8)
/// we need to make sure that the bit_value is in fact the binary value represented by the bits of
/// that bitstring.
#[derive(Clone, Debug)]
pub struct HuffmanCodesBitstringAccumulationTable {
    /// Fixed column to denote whether the constraints will be enabled or not.
    pub q_enabled: Column<Fixed>,
    /// The encoded/decoded data's instance ID where this FSE table belongs.
    pub instance_idx: Column<Advice>,
    /// The frame's ID within the data instance where this FSE table belongs.
    pub frame_idx: Column<Advice>,
    /// The byte offset within the data instance where the encoded FSE table begins. This is
    /// 1-indexed, i.e. byte_offset == 1 at the first byte.
    pub byte_offset: Column<Advice>,
    /// The byte offset of byte_1 in the zstd encoded data. byte_idx' == byte_idx
    /// while 0 <= bit_index < 15. At bit_index == 15, byte_idx' == byte_idx + 1.
    pub byte_idx_1: Column<Advice>,
    /// The byte offset of byte_2 in the zstd encoded data. byte_idx' == byte_idx
    /// while 0 <= bit_index < 15. At bit_index == 15, byte_idx' == byte_idx + 1.
    ///
    /// We also have byte_idx_2 == byte_idx_1 + 1.
    pub byte_idx_2: Column<Advice>,
    /// The byte value at byte_idx_1.
    pub byte_1: Column<Advice>,
    /// The byte value at byte_idx_2.
    pub byte_2: Column<Advice>,
    /// The index within these 2 bytes, i.e. 0 <= bit_index <= 15. bit_index increments until its
    /// 15 and then is reset to 0. Repeats while we finish bitstring accumulation of all bitstrings
    /// used in the Huffman codes.
    pub bit_index: Column<Fixed>,
    /// The bit at bit_index. Accumulation of bits from 0 <= bit_index <= 7 denotes byte_1.
    /// Accumulation of 8 <= bit_index <= 15 denotes byte_2.
    pub bit: Column<Advice>,
    /// The accumulator over 0 <= bit_index <= 7.
    pub bit_value_acc_1: Column<Advice>,
    /// The accumulator over 8 <= bit_index <= 15.
    pub bit_value_acc_2: Column<Advice>,
    /// The accumulator over bits from is_start to is_end, i.e. while is_set == 1.
    pub bit_value_acc: Column<Advice>,
    /// To mark the bit_index at which the bitstring starts.
    pub is_start: Column<Advice>,
    /// To mark the bit_index at which the bitstring ends.
    pub is_end: Column<Advice>,
    /// Boolean that is set from is_start to is_end.
    pub is_set: Column<Advice>,
}

impl HuffmanCodesBitstringAccumulationTable {
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enabled = meta.fixed_column();
        let table = Self {
            q_enabled,
            instance_idx: meta.advice_column(),
            frame_idx: meta.advice_column(),
            byte_offset: meta.advice_column(),
            byte_idx_1: meta.advice_column(),
            byte_idx_2: meta.advice_column(),
            byte_1: meta.advice_column(),
            byte_2: meta.advice_column(),
            bit_index: meta.fixed_column(),
            bit: meta.advice_column(),
            bit_value_acc_1: meta.advice_column(),
            bit_value_acc_2: meta.advice_column(),
            bit_value_acc: meta.advice_column(),
            is_start: meta.advice_column(),
            is_end: meta.advice_column(),
            is_set: meta.advice_column(),
        };

        meta.create_gate("TODO", |meta| {
            let mut cb = BaseConstraintBuilder::default();
            cb.gate(meta.query_fixed(q_enabled, Rotation::cur()))
        });

        table
    }
}

impl<F: Field> LookupTable<F> for HuffmanCodesBitstringAccumulationTable {
    fn columns(&self) -> Vec<halo2_proofs::plonk::Column<halo2_proofs::plonk::Any>> {
        unimplemented!()
    }

    fn annotations(&self) -> Vec<String> {
        unimplemented!()
    }
}
