//! Fuzz target: verify_inclusion must never panic.
//!
//! Feeds arbitrary proof structures to `verify_inclusion` and asserts
//! it returns a bool without panicking. Any panic is a defect.

#![no_main]

use arbitrary::Arbitrary;
use eml::{ProofStep, verify_inclusion};
use libfuzzer_sys::fuzz_target;
use sha2::{Digest, Sha256};

/// Hasher for fuzz context — SHA-256 with domain separation.
#[derive(Debug)]
struct FuzzHasher;

impl eml::Hasher for FuzzHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x00]);
        h.update(data);
        h.finalize().to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        h.update([0x01]);
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn eml::Hasher> {
        Box::new(FuzzHasher)
    }
}

#[derive(Debug, Arbitrary)]
struct FuzzStep {
    siblings: Vec<Vec<u8>>,
    position: usize,
}

#[derive(Debug, Arbitrary)]
struct Input {
    index: u64,
    tree_size: u64,
    arity: u64,
    path: Vec<FuzzStep>,
    leaf_hash: Vec<u8>,
    root: Vec<u8>,
}

fuzz_target!(|input: Input| {
    let path: Vec<ProofStep> = input
        .path
        .into_iter()
        .map(|s| ProofStep {
            siblings: s.siblings,
            position: s.position,
        })
        .collect();
    // Must not panic — result is discarded.
    let _ = verify_inclusion(
        &FuzzHasher,
        &input.leaf_hash,
        input.index,
        input.tree_size,
        input.arity,
        &path,
        &input.root,
    );
});
