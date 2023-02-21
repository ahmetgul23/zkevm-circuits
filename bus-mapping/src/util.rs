//! ..
use eth_types::{Hash, H256};
use ethers_core::utils::keccak256;
use halo2_proofs::halo2curves::{bn256::Fr, group::ff::PrimeField};
use mpt_circuits::hash::MessageHashable;
use once_cell::sync::Lazy;

use std::str::FromStr;

/// ..
pub fn read_env_var<T: Clone + FromStr>(var_name: &'static str, default: T) -> T {
    std::env::var(var_name)
        .map(|s| s.parse::<T>().unwrap_or_else(|_| default.clone()))
        .unwrap_or(default)
}
pub(crate) static CHECK_MEM_STRICT: Lazy<bool> =
    Lazy::new(|| read_env_var("CHECK_MEM_STRICT", false));

/// Define any object can encode the code to a 32 bytes hash
pub trait CodeHash: std::fmt::Debug {
    /// Hash the input bytes
    fn hash_code(&self, code: &[u8]) -> Hash;
    /// Hash of empty bytes
    fn empty_hash(&self) -> Hash;
}

/// Helper trait for clone object in a object-safe way
pub trait CodeHashCopy: CodeHash {
    /// clone to a boxed obect
    fn clone_box(&self) -> Box<dyn CodeHashCopy>;
}

impl<T> CodeHashCopy for T
where
    T: 'static + CodeHash + Clone,
{
    fn clone_box(&self) -> Box<dyn CodeHashCopy> {
        Box::new(self.clone())
    }
}

/// Placeholder struct representing Keccak256 hash of the account code.
#[derive(Debug, Clone)]
pub struct EthCodeHash;

impl CodeHash for EthCodeHash {
    fn hash_code(&self, code: &[u8]) -> Hash {
        H256(keccak256(code))
    }

    fn empty_hash(&self) -> Hash {
        H256(keccak256([]))
    }
}

/// Default number of bytes to pack into a field element.
pub const POSEIDON_HASH_BYTES_IN_FIELD: usize = 16;

/// Represents Poseidon hash of the account code.
#[derive(Debug, Clone)]
pub struct PoseidonCodeHash {
    /// Number of bytes in the field.
    n: usize,
}

impl PoseidonCodeHash {
    /// Build a new instance, provided the number of bytes in field.
    pub fn new(n: usize) -> Self {
        Self { n }
    }
}

impl CodeHash for PoseidonCodeHash {
    fn hash_code(&self, code: &[u8]) -> Hash {
        if code.is_empty() {
            return self.empty_hash();
        }
        let n = self.n;
        let iter = code.chunks_exact(n);

        let mut msgs = iter
            .clone()
            .map(|c| {
                Fr::from_bytes(
                    Hash::from_slice(
                        c.iter()
                            .rev()
                            .cloned()
                            .chain(std::iter::repeat(0).take(n))
                            .collect::<Vec<u8>>()
                            .as_slice(),
                    )
                    .as_fixed_bytes(),
                )
                .unwrap()
            })
            .collect::<Vec<Fr>>();
        if !iter.remainder().is_empty() {
            msgs.push(
                Fr::from_bytes(
                    Hash::from_slice(
                        std::iter::repeat(0)
                            .take(n - iter.remainder().len())
                            .chain(iter.remainder().iter().rev().cloned())
                            .chain(std::iter::repeat(0).take(n))
                            .collect::<Vec<u8>>()
                            .as_slice(),
                    )
                    .as_fixed_bytes(),
                )
                .unwrap(),
            );
        }

        Hash::from_slice(
            Fr::hash_msg(&msgs, Some(code.len() as u64))
                .to_repr()
                .as_ref()
                .iter()
                .cloned()
                .rev()
                .collect::<Vec<u8>>()
                .as_slice(),
        )
    }

    fn empty_hash(&self) -> Hash {
        // // TODO: replace this with the correct empty hash
        let mut hash = [0; 32];
        hash[31] = 6;
        hash.into()
    }
}

#[test]
fn poseidon_code_hashing() {
    let code_hasher = PoseidonCodeHash::new(POSEIDON_HASH_BYTES_IN_FIELD);

    let empty_bytes = [];
    code_hasher.hash_code(&empty_bytes);

    let simple_byte: [u8; 1] = [0];
    assert_eq!(
        format!("{:?}", code_hasher.hash_code(&simple_byte)),
        "0x0ee069e6aa796ef0e46cbd51d10468393d443a00f5affe72898d9ab62e335e16"
    );

    let simple_byte: [u8; 2] = [0, 1];
    assert_eq!(
        format!("{:?}", code_hasher.hash_code(&simple_byte)),
        "0x26cd650aa0d0b9aada79f5f7c03c5961430c12a2142832789fc31a4188d762ff"
    );

    let example = "608060405234801561001057600080fd5b506004361061004c5760003560e01c806321848c46146100515780632e64cec11461006d578063b0f2b72a1461008b578063f3417673146100a7575b600080fd5b61006b60048036038101906100669190610116565b6100c5565b005b6100756100da565b604051610082919061014e565b60405180910390f35b6100a560048036038101906100a09190610116565b6100e3565b005b6100af6100ed565b6040516100bc919061014e565b60405180910390f35b8060008190555060006100d757600080fd5b50565b60008054905090565b8060008190555050565b6000806100f957600080fd5b600054905090565b60008135905061011081610173565b92915050565b60006020828403121561012857600080fd5b600061013684828501610101565b91505092915050565b61014881610169565b82525050565b6000602082019050610163600083018461013f565b92915050565b6000819050919050565b61017c81610169565b811461018757600080fd5b5056fea2646970667358221220f4bca934426c76c7cb87cc32876fc6e65d1d7de23424faa61c347ffed95c449064736f6c63430008040033";
    let bytes = hex::decode(example).unwrap();

    assert_eq!(
        format!("{:?}", code_hasher.hash_code(&bytes)),
        "0x0e6d089fa72b508b90e014b486d64a5311df3030c45b10a95366cf53cd1ec9d5"
    );
}
