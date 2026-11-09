//! The `Hasher` seam — the multihash interface of the kernel.
//!
//! Provides the n-ary hashing operations the tree is built from, plus a null
//! constant. Prefix domain-separation is *not* a kernel axis: an application
//! supplies a prefixing `Hasher` wrapper if it wants one.

use std::fmt::Debug;

/// Hash operations required by the Merkle Spine.
///
/// # Fixed-width contract (per hasher)
///
/// Every digest a single `Hasher` produces — from [`Hasher::leaf`],
/// [`Hasher::node`], [`Hasher::empty`], [`Hasher::null`], and [`Hasher::hash`] —
/// **must** be the same constant byte length, reported by [`Hasher::digest_len`].
/// Within one tree this is what lets the inclusion and consistency verifiers
/// reject any sibling or peak of the wrong width.
///
/// The contract is per hasher, not across hashers. The node hash concatenates
/// child digests **without a length prefix**, and a binding-root node's children
/// are the member roots of *different* algorithms, so they may differ in width
/// (e.g. 32 and 48 bytes). That is sound because a member root extracted from a
/// binding root is only ever used by comparing it to a digest recomputed under
/// its own algorithm's hasher (the spine path check, consistency check, and
/// snapshot leaf proofs); a root cut at the wrong boundary has the wrong length
/// or content and cannot match. [`crate::mr::nary_mr`] therefore does not
/// constrain child widths.
pub trait Hasher: Debug + Send + Sync {
    /// The constant byte length of every digest this hasher produces.
    ///
    /// All of [`Self::leaf`], [`Self::node`], [`Self::empty`], [`Self::null`],
    /// and [`Self::hash`] return exactly this many bytes. See the trait-level
    /// *Fixed-width contract*.
    ///
    /// The default derives the width from [`Self::empty`] — the hash of the
    /// empty string is a digest like any other, so under the fixed-width
    /// contract its length *is* the digest length. A hasher with a cheaper way
    /// to report its width may override; the value must equal the byte length of
    /// every digest it produces.
    #[must_use]
    fn digest_len(&self) -> usize {
        self.empty().len()
    }

    /// Hash leaf data: H(data). No prefix byte.
    ///
    /// Returns [`Self::digest_len`] bytes.
    #[must_use]
    fn leaf(&self, data: &[u8]) -> Vec<u8>;

    /// Hash n children: H(c₁ ‖ c₂ ‖ ... ‖ cₘ). No prefix byte.
    /// Caller guarantees m ≥ 2 (a lone child is handled by promotion).
    ///
    /// Children are concatenated without a length prefix and may differ in width
    /// (binding-root children are other algorithms' roots); see the trait-level
    /// contract. Returns [`Self::digest_len`] bytes.
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
