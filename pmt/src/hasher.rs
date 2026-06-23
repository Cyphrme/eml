//! The `Hasher` seam — the multihash interface of the kernel.
//!
//! Provides the n-ary hashing operations the tree is built from, plus a null
//! constant. Prefix domain-separation is *not* a kernel axis: an application
//! supplies a prefixing `Hasher` wrapper if it wants one.

use std::fmt::Debug;

/// Hash operations required by the Polymorphic Merkle Tree.
pub trait Hasher: Debug + Send + Sync {
    /// Hash leaf data: H(data). No prefix byte.
    #[must_use]
    fn leaf(&self, data: &[u8]) -> Vec<u8>;

    /// Hash n children: H(c₁ ‖ c₂ ‖ ... ‖ cₘ). No prefix byte.
    /// Caller guarantees m ≥ 2 (a lone child is handled by promotion).
    #[must_use]
    fn node(&self, children: &[&[u8]]) -> Vec<u8>;

    /// Hash of the empty string. Root of an empty tree.
    #[must_use]
    fn empty(&self) -> Vec<u8>;

    /// Null leaf constant: `H(b"null")`.
    ///
    /// Because `leaf(d) = H(d)`, we have `leaf(b"null") == null()` by
    /// construction.  This identity is intentional and inert: activity is
    /// read from the committed epoch timeline, never inferred from digest
    /// null-ness, so an active cell whose payload is literally `b"null"`
    /// is indistinguishable from an inactive cell only by an observer who
    /// ignores the authenticated timeline — a correct verifier never does.
    ///
    /// Internal node hashes cannot equal `null()` except by a true hash
    /// collision: a node's preimage concatenates ≥ 2 digests (total length
    /// ≥ 2 × digest_len), whereas `b"null"` is 4 bytes; the preimages
    /// differ in length, so a collision requires breaking the hash function.
    #[must_use]
    fn null(&self) -> Vec<u8> {
        self.hash(b"null")
    }

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
