//! Shared k-ary log-spine topology — the proof spine.
//!
//! The proof spine has a fixed arity `k` (`2..=256`). For a given `tree_size`
//! it decomposes into a *frontier* of perfect k-ary subtrees
//! ([`frontier_for_size`]); those frontier nodes are then folded into one root
//! by repeatedly grouping the rightmost `k` of them. The shape of an inclusion
//! proof's log skeleton — how many steps it has and, per step, the path node's
//! position and sibling count — is fully determined by `(tree_size, arity,
//! index)`.
//!
//! This module is the single place that derivation lives. The verifier checks a
//! proof's skeleton field-by-field against [`inclusion_skeleton`]; the generator
//! emits the same skeleton. Keeping one source of truth is what prevents the
//! producer and verifier from drifting into disagreeing topologies.

use std::ops::RangeInclusive;

/// The valid arity range for the proof spine: `2..=256`.
///
/// Every caller that validates or branches on `k` uses this constant so the
/// range is defined exactly once.
pub const ARITY_RANGE: RangeInclusive<u64> = 2..=256;

/// Fold a non-empty frontier of elements into one root by repeatedly grouping
/// the rightmost `k`, identical to the log's own root fold.
///
/// `items` must be non-empty. `merge` combines a group of `k` elements (or the
/// final `2..=k` remainder) into one. For digest folds the caller passes
/// `|chunk| nary_mr(hasher, ...)`.
///
/// This is the single implementation of the grouping loop shared by every
/// frontier-fold site across the crates (the canonical copy lifted from
/// `eml::filling::fold_components`).
///
/// # Panics
///
/// Panics (debug) if `items` is empty or `k < 2`.
#[must_use]
pub fn fold_frontier<T, F>(mut items: Vec<T>, k: usize, merge: F) -> T
where
    F: Fn(&[T]) -> T,
{
    debug_assert!(!items.is_empty(), "fold_frontier: items must be non-empty");
    debug_assert!(k >= 2, "fold_frontier: k must be >= 2");
    if items.len() == 1 {
        return items.into_iter().next().unwrap();
    }
    while items.len() > k {
        let split = items.len() - k;
        let merged = merge(&items[split..]);
        items.truncate(split);
        items.push(merged);
    }
    merge(&items)
}

/// Frontier decomposition of a log of `n` leaves at arity `k`.
///
/// Returns `(left, height)` for each perfect k-ary subtree, left to right.
///
/// # Preconditions
///
/// `k` must be in `2..=256`. All callers are expected to pre-validate arity
/// before calling this function. Violated in debug builds only (no-op in
/// release builds — the caller already checked).
#[must_use]
pub fn frontier_for_size(n: u64, k: u64) -> Vec<(u64, u32)> {
    debug_assert!(
        ARITY_RANGE.contains(&k),
        "frontier_for_size: arity {k} out of range 2..=256; caller must pre-validate"
    );
    let mut frontier = Vec::new();
    let mut curr_left = 0;
    let mut temp_n = n;
    while temp_n > 0 {
        let mut height = 0;
        let mut cap: u64 = 1;
        while let Some(next_cap) = cap.checked_mul(k) {
            if next_cap <= temp_n {
                cap = next_cap;
                height += 1;
            } else {
                break;
            }
        }
        frontier.push((curr_left, height));
        curr_left += cap;
        temp_n -= cap;
    }
    frontier
}

/// One step of a log-spine inclusion skeleton, ordered leaf → root.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SkeletonStep {
    /// Position of the path node among its parent's children (0-indexed).
    pub position: usize,
    /// Number of sibling digests at this step (children count minus one).
    ///
    /// Always `>= 1`: uniform steps inside a frontier subtree carry `k - 1`
    /// siblings, and grouping nodes have `2..=k` children. The log skeleton
    /// therefore never contains a zero-sibling (promoted) step.
    pub sibling_count: usize,
}

/// Compute the log-spine inclusion skeleton for a leaf `index` in a tree of
/// `tree_size` leaves at arity `k`.
///
/// Returns the per-step `(position, sibling_count)` from the leaf's frontier
/// subtree up to the spine root, or `None` when the inputs cannot describe a
/// valid log position (`k` out of range, empty frontier, or `index` outside the
/// covered range).
#[must_use]
pub fn inclusion_skeleton(k: u64, tree_size: u64, index: u64) -> Option<Vec<SkeletonStep>> {
    if !ARITY_RANGE.contains(&k) {
        return None;
    }
    let coords = frontier_for_size(tree_size, k);
    if coords.is_empty() {
        return None;
    }
    let k_usize = k as usize;

    // Locate the perfect frontier subtree that contains `index`.
    let mut target = None;
    for (f_idx, &(left, height)) in coords.iter().enumerate() {
        let cap = k.checked_pow(height)?;
        let limit = left.checked_add(cap)?;
        if index >= left && index < limit {
            target = Some((f_idx, left, height));
            break;
        }
    }
    let (f_idx, left, height) = target?;

    let mut steps = Vec::with_capacity(height as usize);

    // Uniform steps inside the frontier subtree: the base-k digits of the
    // offset, low digit first (leaf → frontier-node root).
    let mut offset = index - left;
    for _ in 0..height {
        steps.push(SkeletonStep {
            position: (offset % k) as usize,
            sibling_count: k_usize - 1,
        });
        offset /= k;
    }

    // Grouping steps: from the frontier node up to the spine root.
    for (position, child_count) in grouping_steps(coords.len(), k_usize, f_idx) {
        steps.push(SkeletonStep {
            position,
            sibling_count: child_count - 1,
        });
    }

    Some(steps)
}

/// The grouping steps a frontier node at `f_idx` traverses to reach the root.
///
/// The frontier is folded by repeatedly merging the rightmost `k` nodes; when
/// `2..=k` remain they merge into the root. Each returned `(position, child_count)`
/// describes one merge the target participates in, ordered from the frontier node
/// up to the root.
fn grouping_steps(coords_len: usize, k: usize, f_idx: usize) -> Vec<(usize, usize)> {
    let mut frontier_len = coords_len;
    let mut target_pos = f_idx;
    let mut steps = Vec::new();
    while frontier_len > k {
        let split = frontier_len - k;
        if target_pos >= split {
            steps.push((target_pos - split, k));
            target_pos = split;
        }
        frontier_len = split + 1;
    }
    if frontier_len > 1 {
        steps.push((target_pos, frontier_len));
    }
    steps
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The skeleton length equals the expected log-level path length
    /// `c + height`, and every step carries at least one sibling.
    #[test]
    fn skeleton_steps_never_promoted() {
        for k in [2u64, 3, 5, 16] {
            for tree_size in 1..=130u64 {
                for index in 0..tree_size {
                    let skeleton =
                        inclusion_skeleton(k, tree_size, index).expect("valid log position");
                    for step in &skeleton {
                        assert!(step.sibling_count >= 1, "k={k} n={tree_size} i={index}");
                        assert!(step.position <= step.sibling_count);
                    }
                }
            }
        }
    }

    /// A singleton tree's honest proof is the empty path.
    #[test]
    fn singleton_skeleton_is_empty() {
        for k in [2u64, 4, 7] {
            assert_eq!(inclusion_skeleton(k, 1, 0), Some(Vec::new()));
        }
    }

    #[test]
    fn rejects_out_of_range() {
        assert_eq!(inclusion_skeleton(1, 4, 0), None);
        assert_eq!(inclusion_skeleton(257, 4, 0), None);
        assert_eq!(inclusion_skeleton(2, 0, 0), None);
        assert_eq!(inclusion_skeleton(2, 4, 4), None);
    }
}
