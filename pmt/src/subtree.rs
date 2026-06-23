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
/// The result is byte-identical to a leaf carrying any other payload: the
/// kernel offers no way to tell an embedded subtree root from a raw payload,
/// which is what keeps embedding opaque (no origin branch downstream).
#[must_use]
pub fn embed(root: Vec<u8>) -> Subtree {
    Subtree::Leaf(root)
}

/// Read back the bytes carried by a leaf — the inverse of [`embed`] for a leaf
/// that was constructed from a child root. Returns `None` for an internal node.
#[must_use]
pub fn extract(leaf: &Subtree) -> Option<&[u8]> {
    match leaf {
        Subtree::Leaf(data) => Some(data),
        Subtree::Node(_) => None,
    }
}
