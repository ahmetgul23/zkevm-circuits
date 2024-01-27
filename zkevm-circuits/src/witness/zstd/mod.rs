use eth_types::Field;
use halo2_proofs::circuit::Value;

mod params;
pub use params::*;

mod types;
pub use types::*;

#[cfg(test)]
mod tui;
#[cfg(test)]
use tui::draw_rows;

mod util;
use util::value_bits_le;

/// FrameHeaderDescriptor and FrameContentSize
fn process_frame_header<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
) -> (usize, Vec<ZstdWitnessRow<F>>) {
    let fhd_byte = src
        .get(byte_offset)
        .expect("FrameHeaderDescriptor byte should exist");
    let value_bits = value_bits_le(*fhd_byte);

    assert_eq!(value_bits[0], 0, "dictionary ID should not exist");
    assert_eq!(value_bits[1], 0, "dictionary ID should not exist");
    assert_eq!(value_bits[2], 0, "content checksum should not exist");
    assert_eq!(value_bits[3], 0, "reserved bit should not be set");
    assert_eq!(value_bits[4], 0, "unused bit should not be set");
    assert_eq!(value_bits[5], 1, "single segment expected");

    let fhd_value_rlc =
        last_row.encoded_data.value_rlc * randomness + Value::known(F::from(*fhd_byte as u64));

    // the number of bytes taken to represent FrameContentSize.
    let fcs_tag_len: usize = match value_bits[7] * 2 + value_bits[6] {
        0 => 1,
        1 => 2,
        2 => 4,
        3 => 8,
        _ => unreachable!("2-bit value"),
    };

    // FrameContentSize bytes are read in little-endian, hence its in reverse mode.
    let fcs_bytes = src
        .iter()
        .skip(byte_offset + 1)
        .take(fcs_tag_len)
        .rev()
        .cloned()
        .collect::<Vec<u8>>();
    let fcs = {
        let fcs = fcs_bytes
            .iter()
            .fold(0u64, |acc, &byte| acc * 256u64 + (byte as u64));
        match fcs_tag_len {
            2 => fcs + 256,
            _ => fcs,
        }
    };
    let fcs_tag_value_iter = fcs_bytes
        .iter()
        .scan(Value::known(F::zero()), |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        });
    let fcs_tag_value = fcs_tag_value_iter
        .clone()
        .last()
        .expect("FrameContentSize expected");
    let fcs_value_rlcs = fcs_bytes
        .iter()
        .scan(Value::known(F::zero()), |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        })
        .collect::<Vec<Value<F>>>();
    let aux_1 = fcs_value_rlcs
        .last()
        .expect("FrameContentSize bytes expected");
    let aux_2 = fhd_value_rlc;

    (
        byte_offset + 1 + fcs_tag_len,
        std::iter::once(ZstdWitnessRow {
            state: ZstdState {
                tag: ZstdTag::FrameHeaderDescriptor,
                tag_next: ZstdTag::FrameContentSize,
                tag_len: 1,
                tag_idx: 1,
                tag_value: Value::known(F::from(*fhd_byte as u64)),
                tag_value_acc: Value::known(F::from(*fhd_byte as u64)),
            },
            encoded_data: EncodedData {
                byte_idx: (byte_offset + 1) as u64,
                encoded_len: last_row.encoded_data.encoded_len,
                value_byte: *fhd_byte,
                value_rlc: fhd_value_rlc,
                ..Default::default()
            },
            decoded_data: DecodedData {
                decoded_len: fcs,
                decoded_len_acc: 0,
                total_decoded_len: last_row.decoded_data.total_decoded_len + fcs,
                decoded_byte: 0,
                decoded_value_rlc: last_row.decoded_data.decoded_value_rlc,
            },
            huffman_data: HuffmanData::default(),
            fse_data: FseTableRow::default(),
        })
        .chain(
            fcs_bytes
                .iter()
                .zip(fcs_tag_value_iter)
                .zip(fcs_value_rlcs.iter().rev())
                .enumerate()
                .map(
                    |(i, ((&value_byte, tag_value_acc), &value_rlc))| ZstdWitnessRow {
                        state: ZstdState {
                            tag: ZstdTag::FrameContentSize,
                            tag_next: ZstdTag::BlockHeader,
                            tag_len: fcs_tag_len as u64,
                            tag_idx: (i + 1) as u64,
                            tag_value: fcs_tag_value,
                            tag_value_acc,
                        },
                        encoded_data: EncodedData {
                            byte_idx: (byte_offset + 2 + i) as u64,
                            encoded_len: last_row.encoded_data.encoded_len,
                            value_byte,
                            reverse: true,
                            reverse_idx: (fcs_tag_len - i) as u64,
                            reverse_len: fcs_tag_len as u64,
                            aux_1: *aux_1,
                            aux_2,
                            value_rlc,
                        },
                        decoded_data: last_row.decoded_data.clone(),
                        huffman_data: HuffmanData::default(),
                        fse_data: FseTableRow::default(),
                    },
                ),
        )
        .collect::<Vec<_>>(),
    )
}

fn process_block<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
) -> (usize, Vec<ZstdWitnessRow<F>>, bool) {
    let mut witness_rows = vec![];

    let (byte_offset, rows, last_block, block_type, block_size) =
        process_block_header(src, byte_offset, last_row, randomness);
    witness_rows.extend_from_slice(&rows);

    let last_row = rows.last().expect("last row expected to exist");
    let (_byte_offset, rows) = match block_type {
        BlockType::RawBlock => process_block_raw(
            src,
            byte_offset,
            last_row,
            randomness,
            block_size,
            last_block,
        ),
        BlockType::RleBlock => process_block_rle(
            src,
            byte_offset,
            last_row,
            randomness,
            block_size,
            last_block,
        ),
        BlockType::ZstdCompressedBlock => process_block_zstd(
            src,
            byte_offset,
            last_row,
            randomness,
            block_size,
            last_block,
        ),
        BlockType::Reserved => unreachable!("Reserved block type not expected"),
    };
    witness_rows.extend_from_slice(&rows);

    (byte_offset, witness_rows, last_block)
}

fn process_block_header<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
) -> (usize, Vec<ZstdWitnessRow<F>>, bool, BlockType, usize) {
    let bh_bytes = src
        .iter()
        .skip(byte_offset)
        .take(N_BLOCK_HEADER_BYTES)
        .cloned()
        .collect::<Vec<u8>>();
    let last_block = (bh_bytes[0] & 1) == 1;
    let block_type = BlockType::from((bh_bytes[0] >> 1) & 3);
    let block_size =
        (bh_bytes[2] as usize * 256 * 256 + bh_bytes[1] as usize * 256 + bh_bytes[0] as usize) >> 3;

    let tag_next = match block_type {
        BlockType::RawBlock => ZstdTag::RawBlockBytes,
        BlockType::RleBlock => ZstdTag::RleBlockBytes,
        BlockType::ZstdCompressedBlock => ZstdTag::ZstdBlockLiteralsHeader,
        _ => unreachable!("BlockType::Reserved unexpected"),
    };

    let tag_value_iter = bh_bytes.iter().scan(Value::known(F::zero()), |acc, &byte| {
        *acc = *acc * randomness + Value::known(F::from(byte as u64));
        Some(*acc)
    });
    let tag_value = tag_value_iter.clone().last().expect("BlockHeader expected");

    // BlockHeader follows FrameContentSize which is processed in reverse order.
    // Hence value_rlc at the first BlockHeader byte will be calculated as:
    //
    // value_rlc::cur == aux_1::prev * (rand ^ reverse_len) * rand
    //      + aux_2::prev * rand
    //      + value_byte::cur
    let acc_start = last_row.encoded_data.aux_1
        * randomness.map(|r| r.pow([last_row.encoded_data.reverse_len, 0, 0, 0]))
        + last_row.encoded_data.aux_2;
    let value_rlcs = bh_bytes
        .iter()
        .scan(acc_start, |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        })
        .collect::<Vec<Value<F>>>();

    (
        byte_offset + N_BLOCK_HEADER_BYTES,
        bh_bytes
            .iter()
            .zip(tag_value_iter)
            .zip(value_rlcs.iter())
            .enumerate()
            .map(
                |(i, ((&value_byte, tag_value_acc), &value_rlc))| ZstdWitnessRow {
                    state: ZstdState {
                        tag: ZstdTag::BlockHeader,
                        tag_next,
                        tag_len: N_BLOCK_HEADER_BYTES as u64,
                        tag_idx: (i + 1) as u64,
                        tag_value,
                        tag_value_acc,
                    },
                    encoded_data: EncodedData {
                        byte_idx: (byte_offset + i + 1) as u64,
                        encoded_len: last_row.encoded_data.encoded_len,
                        value_byte,
                        reverse: false,
                        value_rlc,
                        ..Default::default()
                    },
                    decoded_data: last_row.decoded_data.clone(),
                    huffman_data: HuffmanData::default(),
                    fse_data: FseTableRow::default(),
                },
            )
            .collect::<Vec<_>>(),
        last_block,
        block_type,
        block_size,
    )
}

fn process_block_raw<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
    block_size: usize,
    last_block: bool,
) -> (usize, Vec<ZstdWitnessRow<F>>) {
    let value_rlc_iter = src.iter().skip(byte_offset).take(block_size).scan(
        last_row.encoded_data.value_rlc,
        |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    );
    let decoded_value_rlc_iter = src.iter().skip(byte_offset).take(block_size).scan(
        last_row.decoded_data.decoded_value_rlc,
        |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    );
    let tag_value_iter = src.iter().skip(byte_offset).take(block_size).scan(
        Value::known(F::zero()),
        |acc, &byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    );
    let tag_value = tag_value_iter
        .clone()
        .last()
        .expect("Raw bytes must be of non-zero length");
    let tag_next = if last_block {
        ZstdTag::Null
    } else {
        ZstdTag::BlockHeader
    };

    (
        byte_offset + block_size,
        src.iter()
            .skip(byte_offset)
            .take(block_size)
            .zip(tag_value_iter)
            .zip(value_rlc_iter)
            .zip(decoded_value_rlc_iter)
            .enumerate()
            .map(
                |(i, (((&value_byte, tag_value_acc), value_rlc), decoded_value_rlc))| {
                    ZstdWitnessRow {
                        state: ZstdState {
                            tag: ZstdTag::RawBlockBytes,
                            tag_next,
                            tag_len: block_size as u64,
                            tag_idx: (i + 1) as u64,
                            tag_value,
                            tag_value_acc,
                        },
                        encoded_data: EncodedData {
                            byte_idx: (byte_offset + i + 1) as u64,
                            encoded_len: last_row.encoded_data.encoded_len,
                            value_byte,
                            value_rlc,
                            reverse: false,
                            ..Default::default()
                        },
                        decoded_data: DecodedData {
                            decoded_len: last_row.decoded_data.decoded_len,
                            decoded_len_acc: last_row.decoded_data.decoded_len + (i as u64) + 1,
                            total_decoded_len: last_row.decoded_data.total_decoded_len,
                            decoded_byte: value_byte,
                            decoded_value_rlc,
                        },
                        huffman_data: HuffmanData::default(),
                        fse_data: FseTableRow::default(),
                    }
                },
            )
            .collect::<Vec<_>>(),
    )
}

fn process_block_rle<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
    block_size: usize,
    last_block: bool,
) -> (usize, Vec<ZstdWitnessRow<F>>) {
    let rle_byte = src[byte_offset];
    let value_rlc =
        last_row.encoded_data.value_rlc * randomness + Value::known(F::from(rle_byte as u64));
    let decoded_value_rlc_iter = std::iter::repeat(rle_byte).take(block_size).scan(
        last_row.decoded_data.decoded_value_rlc,
        |acc, byte| {
            *acc = *acc * randomness + Value::known(F::from(byte as u64));
            Some(*acc)
        },
    );
    let tag_value = Value::known(F::from(rle_byte as u64));
    let tag_next = if last_block {
        ZstdTag::Null
    } else {
        ZstdTag::BlockHeader
    };

    (
        byte_offset + 1,
        std::iter::repeat(rle_byte)
            .take(block_size)
            .zip(decoded_value_rlc_iter)
            .enumerate()
            .map(|(i, (value_byte, decoded_value_rlc))| ZstdWitnessRow {
                state: ZstdState {
                    tag: ZstdTag::RleBlockBytes,
                    tag_next,
                    tag_len: block_size as u64,
                    tag_idx: (i + 1) as u64,
                    tag_value,
                    tag_value_acc: tag_value,
                },
                encoded_data: EncodedData {
                    byte_idx: (byte_offset + 1) as u64,
                    encoded_len: last_row.encoded_data.encoded_len,
                    value_byte,
                    reverse: false,
                    value_rlc,
                    ..Default::default()
                },
                decoded_data: DecodedData {
                    decoded_len: last_row.decoded_data.decoded_len,
                    decoded_len_acc: last_row.decoded_data.decoded_len_acc + (i as u64) + 1,
                    total_decoded_len: last_row.decoded_data.total_decoded_len,
                    decoded_byte: value_byte,
                    decoded_value_rlc,
                },
                huffman_data: HuffmanData::default(),
                fse_data: FseTableRow::default(),
            })
            .collect::<Vec<_>>(),
    )
}

#[allow(unused_variables)]
fn process_block_zstd<F: Field>(
    src: &[u8],
    byte_offset: usize,
    last_row: &ZstdWitnessRow<F>,
    randomness: Value<F>,
    block_size: usize,
    last_block: bool,
) -> (usize, Vec<ZstdWitnessRow<F>>) {
    unimplemented!();
}

fn process_block_zstd_literals_header<F: Field>() -> (usize, Vec<ZstdWitnessRow<F>>) {
    unimplemented!();
}

fn process_block_zstd_fse<F: Field>() -> (usize, Vec<ZstdWitnessRow<F>>) {
    unimplemented!()
}

fn process_block_zstd_huffman_code<F: Field>() -> (usize, Vec<ZstdWitnessRow<F>>) {
    unimplemented!();
}

fn process_block_zstd_huffman_jump_table<F: Field>() -> (usize, Vec<ZstdWitnessRow<F>>) {
    unimplemented!();
}

fn process_block_zstd_lstream<F: Field>() -> (usize, Vec<ZstdWitnessRow<F>>) {
    unimplemented!();
}

pub fn process<F: Field>(src: &[u8], randomness: Value<F>) -> Vec<ZstdWitnessRow<F>> {
    let mut witness_rows = vec![];
    let byte_offset = 0;

    // FrameHeaderDescriptor and FrameContentSize
    let (byte_offset, rows) = process_frame_header::<F>(
        src,
        byte_offset,
        &ZstdWitnessRow::init(src.len()),
        randomness,
    );
    witness_rows.extend_from_slice(&rows);

    loop {
        let (byte_offset, rows, last_block) = process_block::<F>(
            src,
            byte_offset,
            rows.last().expect("last row expected to exist"),
            randomness,
        );
        witness_rows.extend_from_slice(&rows);

        if last_block {
            assert!(byte_offset >= src.len());
            break;
        }
    }

    #[cfg(test)]
    let _ = draw_rows(&witness_rows);

    witness_rows
}

#[cfg(test)]
mod tests {
    use std::{
        fs::{self, File},
        io::Write,
    };

    #[test]
    #[ignore]
    fn compression_ratio() -> Result<(), std::io::Error> {
        use csv::WriterBuilder;

        let get_compression_ratio = |data: &[u8]| -> f64 {
            let raw_len = data.len();
            let compressed = {
                let mut encoder =
                    zstd::stream::write::Encoder::new(Vec::new(), 0).expect("infallible");
                encoder
                    .set_pledged_src_size(Some(raw_len as u64))
                    .expect("infallible");
                encoder.include_checksum(false).expect("infallible");
                encoder.include_magicbytes(false).expect("infallible");
                encoder.include_contentsize(true).expect("infallible");
                encoder.write_all(data).expect("infallible");
                encoder.finish().expect("infallible")
            };
            let compressed_len = compressed.len();
            raw_len as f64 / compressed_len as f64
        };

        let batches = fs::read_dir("./data")
            .expect("infallible")
            .filter_map(|entry| entry.ok())
            .filter(|entry| entry.file_type().map(|ft| ft.is_file()).unwrap_or(false))
            .map(|entry| fs::read_to_string(entry.path()))
            .filter_map(|data| data.ok())
            .map(|data| hex::decode(data.trim_end()).expect("Failed to decode hex data"))
            .collect::<Vec<Vec<u8>>>();

        let file = File::create("modified-ratio.csv")?;
        let mut writer = WriterBuilder::new().from_writer(file);

        // Write headers to CSV
        writer.write_record(["ID", "Len(input)", "Compression Ratio"])?;

        // Test and store results in CSV
        for (i, batch) in batches.iter().enumerate() {
            let result = get_compression_ratio(batch);

            // Write input and result to CSV
            writer.write_record(&[i.to_string(), batch.len().to_string(), result.to_string()])?;
        }

        // Flush the CSV writer
        writer.flush()?;

        Ok(())
    }

    #[test]
    fn batch_compression() -> Result<(), std::io::Error> {
        use halo2_proofs::halo2curves::bn256::Fr;
        use hex::FromHex;

        use super::*;
        let raw = <Vec<u8>>::from_hex(r#"0100000000000231fb0000000064e588f7000000000000000000000000000000000000000000000000000000000000000000000000007a12000006000000000219f90216038510229a150083039bd49417afd0263d6909ba1f9a8eac697f76532365fb95880234e1a857498000b901a45ae401dc0000000000000000000000000000000000000000000000000000000064e58a1400000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000e404e45aaf0000000000000000000000005300000000000000000000000000000000000004000000000000000000000000d9692f1748afee00face2da35242417dd05a86150000000000000000000000000000000000000000000000000000000000000bb8000000000000000000000000c3100d07a5997a7f9f9cdde967d396f9a2aed6a60000000000000000000000000000000000000000000000000234e1a8574980000000000000000000000000000000000000000000000000049032ac61d5dce9e600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000083104ec1a053077484b4d7a88434c2d03c30c3c55bd3a82b259f339f1c0e1e1244189009c5a01c915dd14aed1b824bf610a95560e380ea3213f0bf345df3bddff1acaf7da84d000002d8f902d5068510229a1500830992fd94bbad0e891922a8a4a7e9c39d4cc0559117016fec87082b6be7f5b757b90264ac9650d800000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000164883164560000000000000000000000005300000000000000000000000000000000000004000000000000000000000000ffd2ece82f7959ae184d10fe17865d27b4f0fb9400000000000000000000000000000000000000000000000000000000000001f4fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffce9f6fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcea0a00000000000000000000000000000000000000000000000000082b6be7f5b75700000000000000000000000000000000000000000000000000000000004c4b40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006aea61ea08dd6e4834cd43a257ed52d9a31dd3b90000000000000000000000000000000000000000000000000000000064e58a1400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000412210e8a0000000000000000000000000000000000000000000000000000000083104ec2a0bc501c59bceb707d958423bad14c0d0daec84ad067f7e42209ad2cb8d904a55da00a04de4c79ed24b7a82d523b5de63c7ff68a3b7bb519546b3fe4ba8bc90a396600000137f9013480850f7eb06980830317329446ce46951d12710d85bc4fe10bb29c6ea501207787019945ca262000b8c4b2dd898a000000000000000000000000000000000000000000000000000000000000002000000000000000000000000065e4e8d7bd50191abfee6e5bcdc4d16ddfe9975e000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000083104ec2a037979a5225dd156f51abf9a8601e9156e1b1308c0474d69af98c55627886232ea048ac197295187e7ad48aa34cc37c2625434fa812449337732d8522014f4eacfc00000137f9013480850f7eb06980830317329446ce46951d12710d85bc4fe10bb29c6ea501207787019945ca262000b8c4b2dd898a000000000000000000000000000000000000000000000000000000000000002000000000000000000000000065e4e8d7bd50191abfee6e5bcdc4d16ddfe9975e000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000083104ec1a087269dbb9e987e5d58ecd3bcb724cbc4e6c843eb9095de16a25263aebfe06f5aa07f3ac49b6847ba51c5319174e51e088117742240f8555c5c1d77108cf0df90d700000137f9013480850f7eb06980830317329446ce46951d12710d85bc4fe10bb29c6ea501207787019945ca262000b8c4b2dd898a000000000000000000000000000000000000000000000000000000000000002000000000000000000000000065e4e8d7bd50191abfee6e5bcdc4d16ddfe9975e000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000083104ec1a04abdb8572dcabf1996825de6f753124eed41c1292fcfdc4d9a90cb4f8a0f8ff1a06ef25857e2cc9d0fa8b6ecc03b4ba6ef6f3ec1515d570fcc9102e2aa653f347a00000137f9013480850f7eb06980830317329446ce46951d12710d85bc4fe10bb29c6ea501207787019945ca262000b8c4b2dd898a000000000000000000000000000000000000000000000000000000000000002000000000000000000000000065e4e8d7bd50191abfee6e5bcdc4d16ddfe9975e000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000083104ec2a0882202163cbb9a299709b443b663fbab459440deabfbe183e999c98c00ea80c2a010ecb1e5196f0b1ee3d067d9a158b47b1376706e42ce2e769cf8e986935781dd"#)
            .expect("FromHex failure");
        let compressed = {
            let mut encoder = zstd::stream::write::Encoder::new(Vec::new(), 0)?;
            encoder.set_pledged_src_size(Some(raw.len() as u64))?;
            encoder.include_checksum(false)?;
            encoder.include_magicbytes(false)?;
            encoder.include_contentsize(true)?;
            encoder.write_all(&raw)?;
            encoder.finish()?
        };

        let _witness_rows = process::<Fr>(&compressed, Value::known(Fr::from(123456789)));

        Ok(())
    }
}
