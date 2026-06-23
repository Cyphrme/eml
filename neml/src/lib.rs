//! `neml` — transitional append-only Merkle log over the [`pmt`] kernel.
//!
//! The kernel surface (the `Hasher` seam, the proof spine, canonicalization,
//! inclusion, embedding, `Sealed`, and epoch construction) lives in [`pmt`] and
//! is re-exported here so existing `neml::*` consumers keep their paths. This
//! crate owns the append-only mechanism (the frontier carry, the tree builder,
//! storage) and the consistency surface ([`proof::ConsistencyProof`]).

pub mod error;
pub mod proof;
pub mod schedule;
pub mod storage;
pub mod tree;

// The kernel surface, re-exported at the historical `neml::*` paths.
pub use error::{Error, Result};
pub use pmt::hasher::{self, Hasher};
pub use pmt::mr::{self, count_leaves, evaluate, nary_mr, within_subtree_path};
pub use pmt::subtree::{self, Subtree};
pub use pmt::topology::{self, SkeletonStep, frontier_for_size, inclusion_skeleton};
pub use pmt::{Sealed, null_digest};
pub use proof::{
    AuditPayload, ConsistencyProof, CouplingProof, InclusionProof, ProofStep, VerifierConfig,
    combined_root_preimage, committed_active_algs, committed_active_at, committed_is_live,
    reconstruct_consistency_roots, reconstruct_inclusion_root, validate_committed_epochs,
    verify_consistency, verify_consistency_with_coupling, verify_epoch_evolution,
    verify_inactivity_with_coupling, verify_inclusion, verify_inclusion_with_coupling,
};
pub use schedule::reduction_count;
pub use storage::{AlgorithmMetas, Epochs, MemoryStorage, Storage};
pub use tree::{LogKind, NaryMerkleLog, TreeConfig};
