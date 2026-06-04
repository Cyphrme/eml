//! Subtree descriptor for structured appends.

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
