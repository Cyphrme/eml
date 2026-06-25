//! The `Hasher` seam — the multihash interface of the kernel.
//!
//! Provides the n-ary hashing operations the tree is built from, plus a null
//! constant. Prefix domain-separation is *not* a kernel axis: an application
//! supplies a prefixing `Hasher` wrapper if it wants one.

use std::fmt::Debug;

/// Hash operations required by the Merkle Spine.
///
/// # Fixed-width contract (load-bearing for binding soundness)
///
/// Every digest a single `Hasher` produces — from [`Hasher::leaf`],
/// [`Hasher::node`], [`Hasher::empty`], [`Hasher::null`], and [`Hasher::hash`] —
/// **must** be the same constant byte length, reported by [`Hasher::digest_len`].
/// The node hash concatenates child digests **without a length prefix**
/// (`node(c₁ ‖ … ‖ cₘ)`); only equal-width children make that concatenation
/// uniquely parseable, so a fixed width is what lets a node digest bind its
/// child-digest *list* (and not merely some other splitting of the same bytes).
///
/// The Lean corpus discharges binding-root soundness over exactly this seam:
/// `combinedChildrenWith_bound` (`proofs/lean/EMLProof/Polydigest.lean`) recovers the
/// committed child-digest list from an equal node hash with **no** uniform-width
/// assumption *in the model* because the model's `Digest` is abstract — the Rust
/// realization supplies that uniformity here, via this contract, so the abstract
/// list-binding maps onto byte-level binding. A variable-width hasher would let
/// distinct child lists share a node preimage without a hash collision, voiding
/// the soundness the proof establishes.
///
/// The fold boundary ([`crate::mr::nary_mr`]) `debug_assert`s that the children
/// it hashes share a width, catching a contract violation in test/debug builds.
pub trait Hasher: Debug + Send + Sync {
    /// The constant byte length of every digest this hasher produces.
    ///
    /// All of [`Self::leaf`], [`Self::node`], [`Self::empty`], [`Self::null`],
    /// and [`Self::hash`] return exactly this many bytes. See the trait-level
    /// *Fixed-width contract*: this width is what makes the unprefixed node-hash
    /// concatenation injective in its child boundaries, on which binding-root
    /// soundness rests.
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
    /// Returns [`Self::digest_len`] bytes (fixed-width contract).
    #[must_use]
    fn leaf(&self, data: &[u8]) -> Vec<u8>;

    /// Hash n children: H(c₁ ‖ c₂ ‖ ... ‖ cₘ). No prefix byte.
    /// Caller guarantees m ≥ 2 (a lone child is handled by promotion).
    ///
    /// Children are concatenated without a length prefix; per the fixed-width
    /// contract every child is [`Self::digest_len`] bytes, so the boundaries are
    /// recoverable. Returns [`Self::digest_len`] bytes.
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
