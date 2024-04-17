/// Number of bits to represent a byte.
pub const N_BITS_PER_BYTE: usize = 8;

pub const N_BLOCK_HEADER_BYTES: usize = 3;

pub const N_MAGIC_NUMBER_BYTES: usize = 4;

/// Maximum number of symbols (weights), i.e. symbol in [0, N_MAX_SYMBOLS).
pub const N_MAX_SYMBOLS: usize = 8;

/// Number of bits used to represent the symbol in binary form. This will be used as a helper
/// gadget to form equality constraints over the symbol's value.
pub const N_BITS_SYMBOL: usize = 3;

pub const MAGIC_NUMBER_BYTES: [u8; N_MAGIC_NUMBER_BYTES] = [0x28, 0xB5, 0x2F, 0xFD];
