//! `neml` — unified n-ary Merkle append-only log tree.

pub mod error;
pub mod hasher;
pub mod mr;
pub mod proof;
pub mod schedule;
pub mod storage;
pub mod subtree;
pub mod tree;

pub use error::{Error, Result};
pub use hasher::Hasher;
pub use mr::{count_leaves, evaluate, nary_mr, within_commit_path};
pub use proof::{
    AuditPayload, ConsistencyProof, CouplingProof, InclusionProof, ProofStep, VerifierConfig,
    reconstruct_consistency_roots, reconstruct_inclusion_root, verify_consistency,
    verify_consistency_with_coupling, verify_inclusion, verify_inclusion_with_coupling,
};
pub use schedule::reduction_count;
pub use storage::{AlgorithmMetas, Epochs, MemoryStorage, Storage};
pub use subtree::Subtree;
pub use tree::{NaryMerkleLog, TreeConfig};

/// The Nothing-Up-My-Sleeve (NUMS) high-entropy 32-byte constant used as the null constant digest.
pub const NULL_DIGEST: &[u8; 32] = &[
    0x24, 0x3f, 0x6a, 0x88, 0x85, 0xa3, 0x08, 0xd3,
    0x13, 0x19, 0x8a, 0x2e, 0x03, 0x70, 0x73, 0x44,
    0xa4, 0x09, 0x38, 0x22, 0x29, 0x9f, 0x31, 0xd0,
    0x08, 0x2e, 0xfa, 0x98, 0xec, 0x4e, 0x6c, 0x89,
];

/// Generate a Nothing-Up-My-Sleeve (NUMS) null digest of a specific target length `digest_len`
/// utilizing a counter-based HKDF-like expansion on the 32-byte `NULL_DIGEST` master seed.
/// This dynamically supports arbitrary multihash sizes without known preimages.
#[must_use]
pub fn generate_nums_null(hasher: &dyn Hasher, digest_len: usize) -> Vec<u8> {
    let mut null_digest = Vec::with_capacity(digest_len);
    let mut counter = 0u64;
    while null_digest.len() < digest_len {
        let mut buf = Vec::with_capacity(32 + 8);
        buf.extend_from_slice(NULL_DIGEST);
        buf.extend_from_slice(&counter.to_be_bytes());
        let chunk = hasher.hash(&buf);
        null_digest.extend_from_slice(&chunk);
        counter += 1;
    }
    null_digest.truncate(digest_len);
    null_digest
}
