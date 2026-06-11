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
pub use mr::{count_leaves, evaluate, nary_mr, within_subtree_path};
pub use proof::{
    AuditPayload, ConsistencyProof, CouplingProof, InclusionProof, ProofStep, VerifierConfig,
    reconstruct_consistency_roots, reconstruct_inclusion_root, verify_consistency,
    verify_consistency_with_coupling, verify_inclusion, verify_inclusion_with_coupling,
};
pub use schedule::reduction_count;
pub use storage::{AlgorithmMetas, Epochs, MemoryStorage, Storage};
pub use subtree::Subtree;
pub use tree::{NaryMerkleLog, TreeConfig};

/// Dynamically generate a null digest constant using the hasher.
#[must_use]
pub fn null_digest(hasher: &dyn Hasher) -> Vec<u8> {
    hasher.hash(b"null")
}


