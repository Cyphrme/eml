//! Hash abstraction for `cyphr-malt`.
//!
//! Extends standard n-ary operations with a null constant and prefix-free
//! hashing semantics.

use std::fmt::Debug;

/// Hash operations required by the unified n-ary Merkle append-only log tree.
pub trait Hasher: Debug + Send + Sync {
    /// Hash leaf data: H(data). No prefix byte.
    #[must_use]
    fn leaf(&self, data: &[u8]) -> Vec<u8>;

    /// Hash n children: H(c₁ ‖ c₂ ‖ ... ‖ cₘ). No prefix byte.
    /// Caller guarantees m ≥ 2 (singletons are handled by promotion).
    #[must_use]
    fn node(&self, children: &[&[u8]]) -> Vec<u8>;

    /// Hash of the empty string. Root of an empty tree.
    #[must_use]
    fn empty(&self) -> Vec<u8>;

    /// Null leaf constant: H(0x02). The single byte `0x02` IS the data hashed.
    #[must_use]
    fn null(&self) -> Vec<u8>;

    /// Raw cryptographic hash of arbitrary data.
    #[must_use]
    fn hash(&self, data: &[u8]) -> Vec<u8>;

    /// Clone the hasher into a box.
    #[must_use]
    fn clone_box(&self) -> Box<dyn Hasher>;
}

impl Clone for Box<dyn Hasher> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}
