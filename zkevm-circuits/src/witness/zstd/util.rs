use super::N_BITS_PER_BYTE;

pub fn value_bits_le(value_byte: u8) -> [u8; N_BITS_PER_BYTE] {
    (0..N_BITS_PER_BYTE)
        .map(|i| (value_byte >> i) & 1u8)
        .collect::<Vec<u8>>()
        .try_into()
        .expect("expected N_BITS_PER_BYTE elements")
}
