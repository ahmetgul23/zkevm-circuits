use eth_types::Field;
use halo2_proofs::circuit::Value;
use strum_macros::EnumIter;

use super::{params::N_BITS_PER_BYTE, util::value_bits_le};

#[derive(Clone, Copy, Debug, EnumIter)]
pub enum FseSymbol {
    S0 = 0,
    S1,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
}

impl From<FseSymbol> for usize {
    fn from(value: FseSymbol) -> Self {
        value as usize
    }
}

pub enum BlockType {
    RawBlock = 0,
    RleBlock,
    ZstdCompressedBlock,
    Reserved,
}

impl From<u8> for BlockType {
    fn from(src: u8) -> Self {
        match src {
            0 => Self::RawBlock,
            1 => Self::RleBlock,
            2 => Self::ZstdCompressedBlock,
            3 => Self::Reserved,
            _ => unreachable!("BlockType is 2 bits"),
        }
    }
}

#[derive(Clone, Copy, Debug, EnumIter)]
pub enum ZstdTag {
    Null = 0,
    MagicNumber,
    FrameHeaderDescriptor,
    FrameContentSize,
    BlockHeader,
    RawBlockBytes,
    RleBlockBytes,
    ZstdBlockLiteralsHeader,
    ZstdBlockHuffmanHeader,
    ZstdBlockHuffmanCode,
    ZstdBlockJumpTable,
    Lstream1,
    Lstream2,
    Lstream3,
    Lstream4,
}

impl ToString for ZstdTag {
    fn to_string(&self) -> String {
        String::from(match self {
            Self::Null => "null",
            Self::MagicNumber => "MagicNumber",
            Self::FrameHeaderDescriptor => "FrameHeaderDescriptor",
            Self::FrameContentSize => "FrameContentSize",
            Self::BlockHeader => "BlockHeader",
            Self::RawBlockBytes => "RawBlockBytes",
            Self::RleBlockBytes => "RleBlockBytes",
            Self::ZstdBlockLiteralsHeader => "ZstdBlockLiteralsHeader",
            Self::ZstdBlockHuffmanHeader => "ZstdBlockHuffmanHeader",
            Self::ZstdBlockHuffmanCode => "ZstdBlockHuffmanCode",
            Self::ZstdBlockJumpTable => "ZstdBlockJumpTable",
            Self::Lstream1 => "Lstream1",
            Self::Lstream2 => "Lstream2",
            Self::Lstream3 => "Lstream3",
            Self::Lstream4 => "Lstream4",
        })
    }
}

#[derive(Clone, Debug)]
pub struct ZstdState<F> {
    pub tag: ZstdTag,
    pub tag_next: ZstdTag,
    pub tag_len: u64,
    pub tag_idx: u64,
    pub tag_value: Value<F>,
    pub tag_value_acc: Value<F>,
}

impl<F: Field> Default for ZstdState<F> {
    fn default() -> Self {
        Self {
            tag: ZstdTag::Null,
            tag_next: ZstdTag::MagicNumber,
            tag_len: 0,
            tag_idx: 0,
            tag_value: Value::known(F::zero()),
            tag_value_acc: Value::known(F::zero()),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct EncodedData<F> {
    pub byte_idx: u64,
    pub encoded_len: u64,
    pub value_byte: u8,
    pub reverse: bool,
    pub reverse_idx: u64,
    pub reverse_len: u64,
    pub aux_1: Value<F>,
    pub aux_2: Value<F>,
    pub value_rlc: Value<F>,
}

impl<F: Field> EncodedData<F> {
    pub fn value_bits_le(&self) -> [u8; N_BITS_PER_BYTE] {
        value_bits_le(self.value_byte)
    }
}

#[derive(Clone, Debug, Default)]
pub struct DecodedData<F> {
    pub decoded_len: u64,
    pub decoded_len_acc: u64,
    pub total_decoded_len: u64,
    pub decoded_byte: u8,
    pub decoded_value_rlc: Value<F>,
}

#[derive(Clone, Debug, Default)]
pub struct HuffmanData {
    pub byte_offset: u64,
    pub bit_value: u8,
    pub k: (u8, u8),
}

#[derive(Clone, Debug, Default)]
pub struct FseData {
    pub idx: u64,
    pub state: u8,
    pub baseline: u8,
    pub num_bits: u8,
    pub symbol: u8,
}

#[derive(Clone, Debug)]
pub struct ZstdWitnessRow<F> {
    pub instance_idx: u64,
    pub frame_idx: u64,
    pub state: ZstdState<F>,
    pub encoded_data: EncodedData<F>,
    pub decoded_data: DecodedData<F>,
    pub huffman_data: HuffmanData,
    pub fse_data: FseData,
}

impl<F: Field> ZstdWitnessRow<F> {
    pub fn init(src_len: usize) -> Self {
        Self {
            instance_idx: 1,
            frame_idx: 0,
            state: ZstdState::default(),
            encoded_data: EncodedData {
                encoded_len: src_len as u64,
                ..Default::default()
            },
            decoded_data: DecodedData::default(),
            huffman_data: HuffmanData::default(),
            fse_data: FseData::default(),
        }
    }
}
