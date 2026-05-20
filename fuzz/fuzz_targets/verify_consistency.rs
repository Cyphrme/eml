//! Fuzz target: verify_consistency must never panic.
//!
//! Feeds arbitrary consistency proof structures and asserts the
//! verifier returns a bool without panicking.

#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sha2::{Digest, Sha256};
use eml::verify_consistency;

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
    fn digest_len(&self) -> usize {
        32
    }
}

#[derive(Debug, Arbitrary)]
struct Input {
    old_size: u64,
    new_size: u64,
    path: Vec<Vec<u8>>,
    old_root: Vec<u8>,
    new_root: Vec<u8>,
}

fuzz_target!(|input: Input| {
    let proof = eml::ConsistencyProof {
        old_size: input.old_size,
        new_size: input.new_size,
        path: input.path,
    };
    let _ = verify_consistency(&FuzzHasher, &proof, &input.old_root, &input.new_root);
});
