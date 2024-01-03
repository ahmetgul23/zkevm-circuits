use eth_types::Field;
use gadgets::binary_number::BinaryNumberConfig;
use halo2_proofs::plonk::{Advice, Column};

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
pub struct FseTable<F> {
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
    pub symbol: BinaryNumberConfig<F, N_BITS_SYMBOL>,
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

impl<F: Field> FseTable<F> {
    pub fn construct() -> Self {
        unimplemented!()
    }
}

impl<F: Field> LookupTable<F> for FseTable<F> {
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
    pub fn construct() -> Self {
        unimplemented!()
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

#[derive(Clone, Debug)]
pub struct HuffmanCodesTable {}

impl HuffmanCodesTable {
    pub fn construct() -> Self {
        unimplemented!()
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

#[derive(Clone, Debug)]
pub struct HuffmanCodesBitstringAccumulationTable {}

impl HuffmanCodesBitstringAccumulationTable {
    pub fn construct() -> Self {
        unimplemented!()
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
