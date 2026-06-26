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
use eml::{Hasher, MemoryStorage, NaryMerkleLog, TreeConfig, verify_consistency, verify_inclusion};
use libfuzzer_sys::fuzz_target;
use sha2::{Digest, Sha256};

#[derive(Debug)]
struct FuzzHasher;

impl Hasher for FuzzHasher {
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

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(FuzzHasher)
    }
}

#[derive(Debug, Arbitrary)]
struct Input {
    /// Number of leaves to append (clamped to 2..=65536).
    leaf_count: u16,
    /// Which leaf to generate an inclusion proof for (mod tree_size).
    target_leaf: u16,
    /// Byte index within the proof path step to mutate (mod path length).
    mutate_path_idx: u8,
    /// Which sibling within the selected step to mutate (mod sibling count).
    mutate_sibling_idx: u8,
    /// Byte offset within the selected sibling to flip (mod sibling length).
    mutate_byte_idx: u8,
    /// Bit to flip (0..7).
    mutate_bit: u8,
    /// Midpoint for consistency proof (mod tree_size, clamped to 1..tree_size).
    consistency_mid: u16,
}

const ARITY: u64 = 2;

fuzz_target!(|input: Input| {
    smol::block_on(async {
        // Clamp leaf count to [2, 65536] — need at least 2 for meaningful proofs.
        let n = (input.leaf_count as u64).max(2);

        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(FuzzHasher),
            TreeConfig { arity: ARITY },
        )
        .await
        .unwrap();

        for i in 0u64..n {
            log.append_leaf(&i.to_le_bytes()).await.unwrap();
        }

        let tree_size = log.size();
        let root = log.root();

        // --- Inclusion proof ---
        let target = (input.target_leaf as u64) % tree_size;
        let inc_proof = match log.inclusion_proof(target, tree_size).await.unwrap() {
            Some(p) => p,
            None => return,
        };
        let leaf_hash = FuzzHasher.leaf(&target.to_le_bytes());
        // The log's concrete MMR skeleton for this leaf's trusted position.
        let skeleton =
            eml::mountain_skeleton(ARITY, tree_size, target).expect("valid log position");

        // Valid proof MUST verify.
        assert!(
            verify_inclusion(&FuzzHasher, &leaf_hash, &skeleton, &inc_proof.path, &root),
            "valid inclusion proof failed to verify"
        );

        // Mutate one bit in the proof path (if non-empty).
        if !inc_proof.path.is_empty() {
            let mut mutated = inc_proof.clone();
            let path_idx = (input.mutate_path_idx as usize) % mutated.path.len();
            let step = &mut mutated.path[path_idx];
            if !step.siblings.is_empty() {
                let sib_idx = (input.mutate_sibling_idx as usize) % step.siblings.len();
                let sib = &mut step.siblings[sib_idx];
                if !sib.is_empty() {
                    let byte_idx = (input.mutate_byte_idx as usize) % sib.len();
                    let bit = input.mutate_bit % 8;
                    sib[byte_idx] ^= 1 << bit;

                    // Mutated proof MUST NOT verify.
                    assert!(
                        !verify_inclusion(&FuzzHasher, &leaf_hash, &skeleton, &mutated.path, &root),
                        "mutated inclusion proof falsely verified!"
                    );
                }
            }
        }

        // --- Consistency proof ---
        if tree_size > 1 {
            let mid = ((input.consistency_mid as u64) % (tree_size - 1)) + 1;

            // Build the old root by constructing a separate log of `mid` leaves.
            let mut old_log = NaryMerkleLog::new(
                MemoryStorage::new(),
                Box::new(FuzzHasher),
                TreeConfig { arity: ARITY },
            )
            .await
            .unwrap();
            for i in 0u64..mid {
                old_log.append_leaf(&i.to_le_bytes()).await.unwrap();
            }
            let old_root = old_log.root();

            let con_proof = match log.consistency_proof(mid, tree_size).await.unwrap() {
                Some(p) => p,
                None => return,
            };

            // Valid proof MUST verify.
            assert!(
                verify_consistency(
                    &FuzzHasher,
                    mid,
                    tree_size,
                    ARITY,
                    &con_proof.boundary_hash,
                    &con_proof.peak_path,
                    &con_proof.new_peaks,
                    con_proof.split_index,
                    &old_root,
                    &root,
                ),
                "valid consistency proof failed to verify"
            );

            // Mutate one bit in the consistency proof path (if non-empty).
            if !con_proof.peak_path.is_empty() {
                let mut mutated = con_proof.clone();
                let path_idx = (input.mutate_path_idx as usize) % mutated.peak_path.len();
                let step = &mut mutated.peak_path[path_idx];
                if !step.siblings.is_empty() {
                    let sib_idx = (input.mutate_sibling_idx as usize) % step.siblings.len();
                    let sib = &mut step.siblings[sib_idx];
                    if !sib.is_empty() {
                        let byte_idx = (input.mutate_byte_idx as usize) % sib.len();
                        let bit = input.mutate_bit % 8;
                        sib[byte_idx] ^= 1 << bit;

                        assert!(
                            !verify_consistency(
                                &FuzzHasher,
                                mid,
                                tree_size,
                                ARITY,
                                &mutated.boundary_hash,
                                &mutated.peak_path,
                                &mutated.new_peaks,
                                mutated.split_index,
                                &old_root,
                                &root,
                            ),
                            "mutated consistency proof falsely verified!"
                        );
                    }
                }
            }
        }
    });
});
