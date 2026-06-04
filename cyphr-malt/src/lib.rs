//! `cyphr-malt` — unified n-ary Merkle append-only log tree.

pub mod error;
pub mod hasher;
pub mod mr;
pub mod schedule;
pub mod storage;
pub mod subtree;

pub use error::{Error, Result};
pub use hasher::Hasher;
pub use mr::{evaluate, nary_mr};
pub use schedule::reduction_count;
pub use storage::{MemoryStorage, Storage};
pub use subtree::Subtree;
