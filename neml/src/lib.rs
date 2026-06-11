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
    committed_active_algs, committed_active_at, committed_is_live, combined_root_preimage,
    reconstruct_consistency_roots, reconstruct_inclusion_root, validate_committed_epochs,
    verify_consistency, verify_consistency_with_coupling, verify_epoch_evolution,
    verify_inclusion, verify_inclusion_with_coupling, verify_inactivity_with_coupling,
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


