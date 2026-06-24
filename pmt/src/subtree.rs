//! Subtree descriptor for structured appends.
//!
//! A leaf carries raw payload bytes. The n-ary subtree recovers full Merkle
//! generality below the proof spine.

/// Describes a subtree to be appended as a single logical unit.
/// Leaves are the atomic data items (czds).
/// Nodes define intermediate n-ary nodes (transactions, commits).
///
/// # Opacity contract
///
/// A `Leaf` is byte-identical whether it carries a raw payload or a child
/// tree's root digest: the kernel **never branches on a leaf's origin**.
/// Callers must never attach an `is_embedded` tag or any other origin marker
/// to a leaf, because doing so would let the kernel inspect origin and break
/// this contract. An auditor cannot tell whether a leaf is a raw payload or
/// an embedded subtree root — that indistinguishability is the security
/// guarantee.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Subtree {
    /// A single leaf containing raw payload bytes.
    ///
    /// Whether those bytes are a raw application payload or a child tree's root
    /// digest is opaque: the kernel treats both identically (no origin tag).
    Leaf(Vec<u8>),
    /// An n-ary internal node with a list of children.
    Node(Vec<Subtree>),
}
