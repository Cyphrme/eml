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

/// The Nothing-Up-My-Sleeve (NUMS) master stream of pi bytes used to generate null constants.
pub const NULL_STREAM: &[u8; 64] = &[
    0x24, 0x3f, 0x6a, 0x88, 0x85, 0xa3, 0x08, 0xd3,
    0x13, 0x19, 0x8a, 0x2e, 0x03, 0x70, 0x73, 0x44,
    0xa4, 0x09, 0x38, 0x22, 0x29, 0x9f, 0x31, 0xd0,
    0x08, 0x2e, 0xfa, 0x98, 0xec, 0x4e, 0x6c, 0x89,
    0x45, 0x28, 0x21, 0xe6, 0x38, 0xd0, 0x13, 0x77,
    0xbe, 0x54, 0x66, 0xcf, 0x34, 0xe9, 0x0c, 0x6c,
    0xc0, 0xac, 0x29, 0xb6, 0x29, 0xb0, 0x8d, 0x7d,
    0x15, 0xd5, 0x02, 0x74, 0x01, 0x7b, 0x89, 0xb7,
];

/// The Nothing-Up-My-Sleeve (NUMS) high-entropy 32-byte constant used as the default null constant digest.
pub const NULL_DIGEST: &[u8; 32] = &[
    0x24, 0x3f, 0x6a, 0x88, 0x85, 0xa3, 0x08, 0xd3,
    0x13, 0x19, 0x8a, 0x2e, 0x03, 0x70, 0x73, 0x44,
    0xa4, 0x09, 0x38, 0x22, 0x29, 0x9f, 0x31, 0xd0,
    0x08, 0x2e, 0xfa, 0x98, 0xec, 0x4e, 0x6c, 0x89,
];

/// Generate a Nothing-Up-My-Sleeve (NUMS) null digest of a specific target length `digest_len`
/// utilizing a slice of the master `NULL_STREAM`.
/// This dynamically supports arbitrary multihash sizes without known preimages.
#[must_use]
pub fn generate_nums_null(_hasher: &dyn Hasher, digest_len: usize) -> Vec<u8> {
    assert!(
        digest_len <= NULL_STREAM.len(),
        "Digest length {} exceeds master NULL_STREAM length {}",
        digest_len,
        NULL_STREAM.len()
    );
    NULL_STREAM[..digest_len].to_vec()
}
