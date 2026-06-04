//! `cyphr-malt` — unified n-ary Merkle append-only log tree.

pub mod hasher;
pub mod mr;
pub mod subtree;

pub use hasher::Hasher;
pub use mr::{evaluate, nary_mr};
pub use subtree::Subtree;
