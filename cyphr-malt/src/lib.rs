//! `cyphr-malt` — unified n-ary Merkle append-only log tree.

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
    ConsistencyProof, InclusionProof, ProofStep, verify_consistency, verify_inclusion,
};
pub use schedule::reduction_count;
pub use storage::{MemoryStorage, Storage};
pub use subtree::Subtree;
pub use tree::{NaryMerkleLog, TreeConfig};
