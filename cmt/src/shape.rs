//! The proof-spine shape, materialized as an explicit positional tree.
//!
//! The CMT is *mutable*, so it cannot reuse the append-only log's frontier
//! (left-subtrees-sealed is unsound once interior cells change). Instead it
//! materializes the proof spine — the same `(size, arity)` → topology the
//! [`spine`] crate pins inclusion proofs against — as an explicit tree of
//! [`ShapeNode`]s over the leaf positions. A single cell's change recomputes only
//! the digests on its root-path, which is what makes both `set` and retroactive
//! per-node algorithm addition cost `O(log n)` rather than a full `O(n)` rebuild.
//!
//! The shape is derived purely from `(size, arity)` by two rules the CMT owns:
//! decompose into a frontier of perfect k-ary subtrees ([`spine::frontier_for_size`],
//! the shared structural primitive), then fold the frontier by repeatedly
//! grouping the rightmost `k` — the **rebalanced** topology. The spine itself is
//! topology-agnostic (it owns no fold); the CMT owns this rebalanced fold and the
//! matching [`rebalanced_skeleton`] the spine verifier pins a proof against, the
//! mutable peer of the append-only log's mountain range. [`crate::Cmt::root`] is
//! property-tested to equal [`spine::evaluate`] over the canonical subtree, so a
//! drift in this shape is caught deterministically.

use spine::{ARITY_RANGE, Hasher, SkeletonStep, fold_frontier, frontier_for_size, nary_mr};

/// One node of the materialized proof spine.
///
/// A `Leaf(position)` names a logical cell; an `Inner(children)` is a hashing
/// node whose children are shape nodes left-to-right. The shape is uniquely
/// determined by `(size, arity)` — never stored, always re-derived — so it
/// stays in lockstep with the spine topology that inclusion proofs check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ShapeNode {
    /// A logical leaf cell at this flat position.
    Leaf(u64),
    /// A hashing inner node over its children, left to right.
    Inner(Vec<ShapeNode>),
}

/// Build the proof-spine shape for `size` leaves at arity `k`.
///
/// Returns `None` when the shape is undefined: `k` out of the spine's
/// `2..=256` range, or an empty tree (`size == 0`) — a CMT always has a root
/// only once it holds at least one cell.
#[must_use]
pub fn build(size: u64, k: u64) -> Option<ShapeNode> {
    if !ARITY_RANGE.contains(&k) || size == 0 {
        return None;
    }
    let coords = frontier_for_size(size, k);
    if coords.is_empty() {
        return None;
    }

    // Each frontier entry is a perfect k-ary subtree rooted at its left index.
    let mut frontier: Vec<ShapeNode> = coords
        .iter()
        .map(|&(left, height)| perfect(left, height, k))
        .collect();

    // Fold the frontier by repeatedly grouping the rightmost `k`, mirroring the
    // spine's `grouping_steps`. When `2..=k` remain they merge into the root.
    let k_usize = k as usize;
    while frontier.len() > k_usize {
        let split = frontier.len() - k_usize;
        let group = frontier.split_off(split);
        frontier.push(ShapeNode::Inner(group));
    }
    if frontier.len() == 1 {
        Some(frontier.pop().expect("len checked == 1"))
    } else {
        Some(ShapeNode::Inner(frontier))
    }
}

/// A perfect k-ary subtree of the given `height`, rooted so its leftmost leaf is
/// flat position `left`. Height 0 is a lone leaf.
pub(crate) fn perfect(left: u64, height: u32, k: u64) -> ShapeNode {
    if height == 0 {
        return ShapeNode::Leaf(left);
    }
    let child_span = k.pow(height - 1);
    let children = (0..k)
        .map(|c| perfect(left + c * child_span, height - 1, k))
        .collect();
    ShapeNode::Inner(children)
}

/// The leftmost flat leaf position covered by `node`.
pub(crate) fn leftmost(node: &ShapeNode) -> u64 {
    match node {
        ShapeNode::Leaf(pos) => *pos,
        ShapeNode::Inner(children) => leftmost(&children[0]),
    }
}

/// The rightmost flat leaf position covered by `node`.
pub(crate) fn rightmost(node: &ShapeNode) -> u64 {
    match node {
        ShapeNode::Leaf(pos) => *pos,
        ShapeNode::Inner(children) => rightmost(children.last().expect("inner node has children")),
    }
}

/// Whether `node` covers flat position `index`.
pub(crate) fn covers(node: &ShapeNode, index: u64) -> bool {
    leftmost(node) <= index && index <= rightmost(node)
}

/// The CMT's concrete inclusion skeleton for `index` in a tree of `size` leaves
/// at arity `k` — the rebalanced topology the spine verifier pins a proof
/// against.
///
/// Walks the [`build`] shape from the root down to the leaf, emitting one
/// [`SkeletonStep`] per inner node on the path; the steps are returned leaf →
/// root, matching the proof path order. Returns `None` for an undefined shape
/// (`k` out of range, `size == 0`, or `index >= size`).
///
/// This is the mutable peer of the append-only log's `mountain_skeleton`: the
/// spine owns no concrete topology, so the CMT supplies its own. `build` is the
/// single shape source, so the producer's `inclusion_path` and this verifier
/// skeleton cannot drift.
#[must_use]
pub fn rebalanced_skeleton(size: u64, k: u64, index: u64) -> Option<Vec<SkeletonStep>> {
    if index >= size {
        return None;
    }
    let shape = build(size, k)?;
    let mut steps = Vec::new();
    descend_skeleton(&shape, index, &mut steps);
    // `descend_skeleton` pushes root → leaf; the proof path is leaf → root.
    steps.reverse();
    Some(steps)
}

/// Push one [`SkeletonStep`] per inner node on the root → leaf path to `index`,
/// in root → leaf order. A lone-child inner node never occurs in `build` (a
/// perfect subtree or a `2..=k` group), so every emitted step hashes.
fn descend_skeleton(node: &ShapeNode, index: u64, out: &mut Vec<SkeletonStep>) {
    if let ShapeNode::Inner(children) = node {
        let position = children
            .iter()
            .position(|c| covers(c, index))
            .expect("the path index is covered by exactly one child");
        out.push(SkeletonStep {
            position,
            sibling_count: children.len() - 1,
        });
        descend_skeleton(&children[position], index, out);
    }
}

/// Bag a frontier's peaks into the CMT member root under `hasher` — the
/// rebalanced fold, grouping the rightmost `k` (the mutable peer of the
/// append-only log's backward-bag). Mirrors [`build`]'s grouping so the folded
/// member root equals the live [`crate::Cmt::root`] over the same peaks. An empty
/// peak set is the empty-tree root.
#[must_use]
pub fn rebalanced_bag(hasher: &dyn Hasher, peaks: &[Vec<u8>], k: u64) -> Vec<u8> {
    if peaks.is_empty() {
        return hasher.empty();
    }
    fold_frontier(peaks.to_vec(), k as usize, |chunk| {
        let refs: Vec<&[u8]> = chunk.iter().map(|v| v.as_slice()).collect();
        nary_mr(hasher, &refs)
    })
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
        assert_eq!(build(1, 2), Some(ShapeNode::Leaf(0)));
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

    fn collect_leaves(node: &ShapeNode, out: &mut Vec<u64>) {
        match node {
            ShapeNode::Leaf(p) => out.push(*p),
            ShapeNode::Inner(children) => {
                for c in children {
                    collect_leaves(c, out);
                }
            },
        }
    }
}
