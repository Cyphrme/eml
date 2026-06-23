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

use std::collections::BTreeMap;

use pmt::ProofStep;

use crate::spine::{self, SpineNode};

/// Build the inclusion path (leaf → root) for `index` over `shape`.
///
/// `leaf_digest` supplies a cell's leaf digest by flat position; `node`
/// hashes children. `cache` is the algorithm's materialized digest cache,
/// keyed by `(leftmost, rightmost)` — off-path siblings read from it first so
/// proof generation is `O(log n)` rather than `O(n)`.
///
/// Emits one [`ProofStep`] per inner node on the path, its `siblings` being
/// the other children's digests in order — exactly the shape
/// [`pmt::proof::reconstruct_inclusion_root`] reconstructs against. The spine
/// build never produces a lone-child inner node, so every emitted step hashes
/// (the kernel rejects a zero-sibling step), preserving proof uniqueness.
pub(crate) fn inclusion_path(
    shape: &SpineNode,
    index: u64,
    cache: &BTreeMap<(u64, u64), Vec<u8>>,
    leaf_digest: &mut dyn FnMut(u64) -> Vec<u8>,
    node: &mut dyn FnMut(&[&[u8]]) -> Vec<u8>,
) -> Vec<ProofStep> {
    let mut path = Vec::new();
    descend(shape, index, cache, leaf_digest, node, &mut path);
    path
}

/// Returns the digest of `cur` and pushes the steps from the leaf up. Steps are
/// pushed leaf-first (the deepest recursion pushes first), matching the kernel's
/// leaf → root path order.
fn descend(
    cur: &SpineNode,
    index: u64,
    cache: &BTreeMap<(u64, u64), Vec<u8>>,
    leaf_digest: &mut dyn FnMut(u64) -> Vec<u8>,
    node: &mut dyn FnMut(&[&[u8]]) -> Vec<u8>,
    path: &mut Vec<ProofStep>,
) -> Vec<u8> {
    match cur {
        SpineNode::Leaf(pos) => leaf_digest(*pos),
        SpineNode::Inner(children) => {
            let position = children
                .iter()
                .position(|c| spine::covers(c, index))
                .expect("the path index is covered by exactly one child");

            // Digest every child; recurse into the one on the path.
            let mut child_digests: Vec<Vec<u8>> = Vec::with_capacity(children.len());
            for (i, child) in children.iter().enumerate() {
                if i == position {
                    child_digests.push(descend(child, index, cache, leaf_digest, node, path));
                } else {
                    child_digests.push(eval(child, cache, leaf_digest, node, &mut 0));
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
///
/// Reads from `cache` first — keyed by the node's `(leftmost, rightmost)`
/// interval — so off-path siblings cost one cache lookup rather than a full
/// subtree traversal. Falls back to recursive evaluation only on a cache miss.
/// When `miss_counter` is provided, increments it on each cache miss.
fn eval(
    cur: &SpineNode,
    cache: &BTreeMap<(u64, u64), Vec<u8>>,
    leaf_digest: &mut dyn FnMut(u64) -> Vec<u8>,
    node: &mut dyn FnMut(&[&[u8]]) -> Vec<u8>,
    miss_counter: &mut usize,
) -> Vec<u8> {
    let key = (spine::leftmost(cur), spine::rightmost(cur));
    if let Some(cached) = cache.get(&key) {
        return cached.clone();
    }
    *miss_counter += 1;
    match cur {
        SpineNode::Leaf(pos) => leaf_digest(*pos),
        SpineNode::Inner(children) => {
            let digests: Vec<Vec<u8>> = children
                .iter()
                .map(|c| eval(c, cache, leaf_digest, node, miss_counter))
                .collect();
            let refs: Vec<&[u8]> = digests.iter().map(Vec::as_slice).collect();
            node(&refs)
        },
    }
}

/// Like [`inclusion_path`] but also returns the number of off-path cache misses.
/// A fully materialized cache produces zero misses; any positive count means
/// some off-path subtree was re-evaluated instead of being served from cache.
#[cfg(test)]
pub(crate) fn inclusion_path_with_miss_count(
    shape: &SpineNode,
    index: u64,
    cache: &BTreeMap<(u64, u64), Vec<u8>>,
    leaf_digest: &mut dyn FnMut(u64) -> Vec<u8>,
    node: &mut dyn FnMut(&[&[u8]]) -> Vec<u8>,
) -> (Vec<ProofStep>, usize) {
    let mut path = Vec::new();
    let mut misses = 0usize;
    descend_counted(
        shape,
        index,
        cache,
        leaf_digest,
        node,
        &mut path,
        &mut misses,
    );
    (path, misses)
}

#[cfg(test)]
fn descend_counted(
    cur: &SpineNode,
    index: u64,
    cache: &BTreeMap<(u64, u64), Vec<u8>>,
    leaf_digest: &mut dyn FnMut(u64) -> Vec<u8>,
    node: &mut dyn FnMut(&[&[u8]]) -> Vec<u8>,
    path: &mut Vec<ProofStep>,
    misses: &mut usize,
) -> Vec<u8> {
    match cur {
        SpineNode::Leaf(pos) => leaf_digest(*pos),
        SpineNode::Inner(children) => {
            let position = children
                .iter()
                .position(|c| spine::covers(c, index))
                .expect("the path index is covered by exactly one child");

            let mut child_digests: Vec<Vec<u8>> = Vec::with_capacity(children.len());
            for (i, child) in children.iter().enumerate() {
                if i == position {
                    child_digests.push(descend_counted(
                        child,
                        index,
                        cache,
                        leaf_digest,
                        node,
                        path,
                        misses,
                    ));
                } else {
                    child_digests.push(eval(child, cache, leaf_digest, node, misses));
                }
            }

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
