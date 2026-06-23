//! The proof-spine shape, materialized as an explicit positional tree.
//!
//! The EMT is *mutable*, so it cannot reuse EML's frontier (left-subtrees-sealed
//! is unsound once interior cells change). Instead it materializes the proof
//! spine — the same `(size, arity)` → topology the kernel pins inclusion proofs
//! against — as an explicit tree of [`SpineNode`]s over the leaf positions. A
//! single cell's change recomputes only the digests on its root-path, which is
//! what makes both `set` and retroactive per-node algorithm addition cost
//! `O(log n)` rather than a full `O(n)` rebuild.
//!
//! The shape is derived purely from `(size, arity)` by the same two rules the
//! kernel's [`pmt::topology`] uses: decompose into a frontier of perfect k-ary
//! subtrees, then fold the frontier by repeatedly grouping the rightmost `k`.
//! Keeping the shape derivation here aligned with the kernel is load-bearing —
//! [`crate::Emt::root`] is property-tested to equal `pmt::evaluate` over the
//! canonical subtree, so a drift in this shape is caught deterministically.

use pmt::topology::frontier_for_size;

/// One node of the materialized proof spine.
///
/// A `Leaf(position)` names a logical cell; an `Inner(children)` is a hashing
/// node whose children are spine nodes left-to-right. The shape is uniquely
/// determined by `(size, arity)` — never stored, always re-derived — so it
/// stays in lockstep with the kernel topology that inclusion proofs check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpineNode {
    /// A logical leaf cell at this flat position.
    Leaf(u64),
    /// A hashing inner node over its children, left to right.
    Inner(Vec<SpineNode>),
}

/// Build the proof-spine shape for `size` leaves at arity `k`.
///
/// Returns `None` when the shape is undefined: `k` out of the kernel's
/// `2..=256` range, or an empty tree (`size == 0`) — an EMT always has a root
/// only once it holds at least one cell.
#[must_use]
pub fn build(size: u64, k: u64) -> Option<SpineNode> {
    if !(2..=256).contains(&k) || size == 0 {
        return None;
    }
    let coords = frontier_for_size(size, k);
    if coords.is_empty() {
        return None;
    }

    // Each frontier entry is a perfect k-ary subtree rooted at its left index.
    let mut frontier: Vec<SpineNode> = coords
        .iter()
        .map(|&(left, height)| perfect(left, height, k))
        .collect();

    // Fold the frontier by repeatedly grouping the rightmost `k`, mirroring the
    // kernel's `grouping_steps`. When `2..=k` remain they merge into the root.
    let k_usize = k as usize;
    while frontier.len() > k_usize {
        let split = frontier.len() - k_usize;
        let group = frontier.split_off(split);
        frontier.push(SpineNode::Inner(group));
    }
    if frontier.len() == 1 {
        Some(frontier.pop().expect("len checked == 1"))
    } else {
        Some(SpineNode::Inner(frontier))
    }
}

/// A perfect k-ary subtree of the given `height`, rooted so its leftmost leaf is
/// flat position `left`. Height 0 is a lone leaf.
fn perfect(left: u64, height: u32, k: u64) -> SpineNode {
    if height == 0 {
        return SpineNode::Leaf(left);
    }
    let child_span = k.pow(height - 1);
    let children = (0..k)
        .map(|c| perfect(left + c * child_span, height - 1, k))
        .collect();
    SpineNode::Inner(children)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_undefined_shapes() {
        assert_eq!(build(0, 2), None);
        assert_eq!(build(4, 1), None);
        assert_eq!(build(4, 257), None);
    }

    #[test]
    fn singleton_is_a_lone_leaf() {
        assert_eq!(build(1, 2), Some(SpineNode::Leaf(0)));
    }

    /// Every flat position `0..size` appears exactly once, left to right.
    #[test]
    fn covers_every_position_in_order() {
        for k in [2u64, 3, 5] {
            for size in 1..=64u64 {
                let mut seen = Vec::new();
                collect_leaves(&build(size, k).expect("defined"), &mut seen);
                let expected: Vec<u64> = (0..size).collect();
                assert_eq!(seen, expected, "k={k} size={size}");
            }
        }
    }

    fn collect_leaves(node: &SpineNode, out: &mut Vec<u64>) {
        match node {
            SpineNode::Leaf(p) => out.push(*p),
            SpineNode::Inner(children) => {
                for c in children {
                    collect_leaves(c, out);
                }
            },
        }
    }
}
