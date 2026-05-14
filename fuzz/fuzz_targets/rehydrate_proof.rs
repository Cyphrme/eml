//! Fuzz target: rehydrate_inclusion_proof must never panic.
//!
//! Feeds arbitrary elided proof structures and asserts the rehydration
//! function returns an InclusionProof without panicking.

#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sha2::{Digest, Sha256};
use tsml::rehydrate_inclusion_proof;

#[derive(Debug)]
struct FuzzHasher;

impl tsml::Hasher for FuzzHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x00]);
        h.update(data);
        h.finalize().to_vec()
    }
    fn node(&self, left: &[u8], right: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01]);
        h.update(left);
        h.update(right);
        h.finalize().to_vec()
    }
    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }
    fn null(&self) -> Vec<u8> {
        Sha256::digest([0x02]).to_vec()
    }
    fn digest_len(&self) -> usize {
        32
    }
}

#[derive(Debug, Arbitrary)]
struct Input {
    index: u64,
    tree_size: u64,
    /// Each entry: None = elided, Some(bytes) = real sibling.
    path: Vec<Option<Vec<u8>>>,
}

fuzz_target!(|input: Input| {
    let elided = tsml::ElidedInclusionProof {
        index: input.index,
        tree_size: input.tree_size,
        path: input.path,
    };
    let _ = rehydrate_inclusion_proof(&elided, &FuzzHasher);
});
