//! Fuzz target: verify_inclusion must never panic.
//!
//! Feeds arbitrary proof structures to `verify_inclusion` and asserts
//! it returns a bool without panicking. Any panic is a defect.

#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sha2::{Digest, Sha256};
use eml::verify_inclusion;

/// Hasher for fuzz context — SHA-256 with RFC 9162 domain separation.
#[derive(Debug)]
struct FuzzHasher;

impl eml::Hasher for FuzzHasher {
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
}

#[derive(Debug, Arbitrary)]
struct Input {
    index: u64,
    tree_size: u64,
    /// Sibling hashes — up to 64 entries (log2(u64::MAX)).
    path: Vec<Vec<u8>>,
    leaf_hash: Vec<u8>,
    root: Vec<u8>,
}

fuzz_target!(|input: Input| {
    let proof = eml::InclusionProof {
        index: input.index,
        tree_size: input.tree_size,
        path: input.path,
    };
    // Must not panic — result is discarded.
    let _ = verify_inclusion(&FuzzHasher, &input.leaf_hash, &proof, &input.root);
});
