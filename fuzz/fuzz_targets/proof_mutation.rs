//! Fuzz target: proof mutation oracle.
//!
//! Builds a real EML log from fuzzer-controlled parameters, generates
//! valid proofs, then mutates a single byte in the proof path. Asserts:
//! - Valid proofs verify (false-negative detection)
//! - Mutated proofs do NOT verify (false-positive detection)
//!
//! Any counterexample is a critical security defect.

#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sha2::{Digest, Sha256};
use eml::{Hasher, Log, MemoryStorage, verify_consistency, verify_inclusion};

#[derive(Debug)]
struct FuzzHasher;

impl Hasher for FuzzHasher {
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
    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }
}

#[derive(Debug, Arbitrary)]
struct Input {
    /// Number of leaves to append (clamped to 2..=65536).
    leaf_count: u16,
    /// Which leaf to generate an inclusion proof for (mod tree_size).
    target_leaf: u16,
    /// Byte index within the proof path to mutate (mod path length).
    mutate_path_idx: u8,
    /// Byte offset within the selected path entry to flip (mod entry length).
    mutate_byte_idx: u8,
    /// Bit to flip (0..7).
    mutate_bit: u8,
    /// Midpoint for consistency proof (mod tree_size, clamped to 1..tree_size).
    consistency_mid: u16,
}

fuzz_target!(|input: Input| {
    smol::block_on(async {
        // Clamp leaf count to [2, 65536] — need at least 2 for meaningful proofs.
        let n = (input.leaf_count as u64).max(2);

        let mut log = Log::new(MemoryStorage::new());
        log.add_algorithm(0, Box::new(FuzzHasher)).await.unwrap();
        for i in 0..n {
            log.append(&i.to_le_bytes()).await.unwrap();
        }

        let tree_size = log.tree_size(0).await.unwrap();
        let root = log.root(0).unwrap();

        // --- Inclusion proof ---
        let target = (input.target_leaf as u64) % tree_size;
        let inc_proof = log.inclusion_proof(0, target).await.unwrap();
        let leaf_hash = FuzzHasher.leaf(&(target as u64).to_le_bytes());

        // Valid proof MUST verify.
        assert!(
            verify_inclusion(&FuzzHasher, &leaf_hash, &inc_proof, &root),
            "valid inclusion proof failed to verify"
        );

        // Mutate one bit in the proof path (if non-empty).
        if !inc_proof.path.is_empty() {
            let mut mutated = inc_proof.clone();
            let path_idx = (input.mutate_path_idx as usize) % mutated.path.len();
            if !mutated.path[path_idx].is_empty() {
                let byte_idx = (input.mutate_byte_idx as usize) % mutated.path[path_idx].len();
                let bit = input.mutate_bit % 8;
                mutated.path[path_idx][byte_idx] ^= 1 << bit;

                // Mutated proof MUST NOT verify.
                assert!(
                    !verify_inclusion(&FuzzHasher, &leaf_hash, &mutated, &root),
                    "mutated inclusion proof falsely verified!"
                );
            }
        }

        // --- Consistency proof ---
        if tree_size > 1 {
            let mid = ((input.consistency_mid as u64) % (tree_size - 1)) + 1;

            // Build the old root by constructing a separate log of `mid` leaves.
            let mut old_log = Log::new(MemoryStorage::new());
            old_log.add_algorithm(0, Box::new(FuzzHasher)).await.unwrap();
            for i in 0..mid {
                old_log.append(&i.to_le_bytes()).await.unwrap();
            }
            let old_root = old_log.root(0).unwrap();

            let con_proof = log.consistency_proof(0, mid).await.unwrap();

            // Valid proof MUST verify.
            assert!(
                verify_consistency(&FuzzHasher, &con_proof, &old_root, &root),
                "valid consistency proof failed to verify"
            );

            // Mutate one bit in the consistency proof path (if non-empty).
            if !con_proof.path.is_empty() {
                let mut mutated = con_proof.clone();
                let path_idx = (input.mutate_path_idx as usize) % mutated.path.len();
                if !mutated.path[path_idx].is_empty() {
                    let byte_idx = (input.mutate_byte_idx as usize) % mutated.path[path_idx].len();
                    let bit = input.mutate_bit % 8;
                    mutated.path[path_idx][byte_idx] ^= 1 << bit;

                    assert!(
                        !verify_consistency(&FuzzHasher, &mutated, &old_root, &root),
                        "mutated consistency proof falsely verified!"
                    );
                }
            }
        }
    });
});
