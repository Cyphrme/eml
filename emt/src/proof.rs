//! Inclusion and non-membership proof generation over the materialized spine.
//!
//! Both reuse the kernel's proof machinery: the path produced here verifies with
//! [`pmt::verify_inclusion`] against the trusted `(index, tree_size, arity,
//! root)` topology. The EMT shares the kernel index space, so it is *not* a
//! second proof system — it only generates paths the kernel checks.
//!
//! **Non-membership** is inclusion of the kernel null constant at a position
//! (SAD §5): a cell that carries no real value hashes to `null()`, and an
//! inclusion proof for `null()` at that index is the membership-of-null witness.
//! It rests on the same collapse/promotion canonical encoding as inclusion, so
//! it needs no separate verifier.

use pmt::proof::ProofStep;

use crate::spine::SpineNode;

/// Build the inclusion path (leaf → root) for `index` over `shape`.
///
/// `leaf_digest` supplies a cell's leaf digest by flat position; `node`
/// hashes children. Emits one [`ProofStep`] per inner node on the path, its
/// `siblings` being the other children's digests in order — exactly the shape
/// [`pmt::proof::reconstruct_inclusion_root`] reconstructs against. The spine
/// build never produces a lone-child inner node, so every emitted step hashes
/// (the kernel rejects a zero-sibling step), preserving proof uniqueness.
pub(crate) fn inclusion_path(
    shape: &SpineNode,
    index: u64,
    leaf_digest: &mut dyn FnMut(u64) -> Vec<u8>,
    node: &mut dyn FnMut(&[&[u8]]) -> Vec<u8>,
) -> Vec<ProofStep> {
    let mut path = Vec::new();
    descend(shape, index, leaf_digest, node, &mut path);
    path
}

/// Returns the digest of `cur` and pushes the steps from the leaf up. Steps are
/// pushed leaf-first (the deepest recursion pushes first), matching the kernel's
/// leaf → root path order.
fn descend(
    cur: &SpineNode,
    index: u64,
    leaf_digest: &mut dyn FnMut(u64) -> Vec<u8>,
    node: &mut dyn FnMut(&[&[u8]]) -> Vec<u8>,
    path: &mut Vec<ProofStep>,
) -> Vec<u8> {
    match cur {
        SpineNode::Leaf(pos) => leaf_digest(*pos),
        SpineNode::Inner(children) => {
            let position = children
                .iter()
                .position(|c| covers(c, index))
                .expect("the path index is covered by exactly one child");

            // Digest every child; recurse into the one on the path.
            let mut child_digests: Vec<Vec<u8>> = Vec::with_capacity(children.len());
            for (i, child) in children.iter().enumerate() {
                if i == position {
                    child_digests.push(descend(child, index, leaf_digest, node, path));
                } else {
                    child_digests.push(eval(child, leaf_digest, node));
                }
            }

            // This node's own step: the siblings are every child but the one on
            // the path, in order.
            let siblings: Vec<Vec<u8>> = child_digests
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != position)
                .map(|(_, d)| d.clone())
                .collect();
            path.push(ProofStep { siblings, position });

            let refs: Vec<&[u8]> = child_digests.iter().map(Vec::as_slice).collect();
            node(&refs)
        },
    }
}

/// Evaluate a whole subtree's digest (no path bookkeeping).
fn eval(
    cur: &SpineNode,
    leaf_digest: &mut dyn FnMut(u64) -> Vec<u8>,
    node: &mut dyn FnMut(&[&[u8]]) -> Vec<u8>,
) -> Vec<u8> {
    match cur {
        SpineNode::Leaf(pos) => leaf_digest(*pos),
        SpineNode::Inner(children) => {
            let digests: Vec<Vec<u8>> = children
                .iter()
                .map(|c| eval(c, leaf_digest, node))
                .collect();
            let refs: Vec<&[u8]> = digests.iter().map(Vec::as_slice).collect();
            node(&refs)
        },
    }
}

fn leftmost(node: &SpineNode) -> u64 {
    match node {
        SpineNode::Leaf(pos) => *pos,
        SpineNode::Inner(children) => leftmost(&children[0]),
    }
}

fn rightmost(node: &SpineNode) -> u64 {
    match node {
        SpineNode::Leaf(pos) => *pos,
        SpineNode::Inner(children) => rightmost(children.last().expect("inner node has children")),
    }
}

fn covers(node: &SpineNode, index: u64) -> bool {
    leftmost(node) <= index && index <= rightmost(node)
}
