//! `cyphr-malt` — unified n-ary Merkle append-only log tree.

pub mod hasher;
pub mod mr;
pub mod schedule;
pub mod subtree;

pub use hasher::Hasher;
pub use mr::{evaluate, nary_mr};
pub use schedule::reduction_count;
pub use subtree::Subtree;
