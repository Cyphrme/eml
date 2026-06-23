//! Subtree descriptor for structured appends, and the embedding surface.
//!
//! A leaf carries raw payload bytes. Embedding is opaque: a child tree's root
//! embeds as a leaf, byte-identical to a raw-payload leaf, so the kernel never
//! branches on a leaf's origin (there is no `is_embedded` tag). The n-ary
//! subtree recovers full Merkle generality below the proof spine.

/// Describes a subtree to be appended as a single logical unit.
/// Leaves are the atomic data items (czds).
/// Nodes define intermediate n-ary nodes (transactions, commits).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Subtree {
    /// A single leaf containing raw payload data.
    Leaf(Vec<u8>),
    /// An n-ary internal node with a list of children.
    Node(Vec<Subtree>),
}

/// Embed a child tree's `root` digest as an opaque kernel leaf.
///
/// The embedded leaf is **byte-identical to a raw-payload leaf carrying the
/// same bytes**: the kernel never branches on a leaf's origin. This
/// indistinguishability is the *opacity contract* — embedding must never
/// attach a tag or marker, because doing so would let the kernel inspect
/// origin and break the contract. Callers rely on it for security: an
/// auditor cannot tell whether a leaf is a raw payload or an embedded subtree
/// root, so embedded sub-trees cannot be fingerprinted.
#[must_use]
#[inline]
pub fn embed(root: Vec<u8>) -> Subtree {
    Subtree::Leaf(root)
}

/// Read back the bytes carried by a leaf — the inverse of [`embed`] for a leaf
/// that was constructed from a child root. Returns `None` for an internal node.
///
/// Because [`embed`] is opaque, `extract` simply returns the raw bytes; it
/// carries no proof that those bytes originated from [`embed`] rather than a
/// raw-payload append. Callers who need that guarantee must track origin
/// themselves.
#[must_use]
#[inline]
pub fn extract(leaf: &Subtree) -> Option<&[u8]> {
    match leaf {
        Subtree::Leaf(data) => Some(data),
        Subtree::Node(_) => None,
    }
}
