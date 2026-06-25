//! Shared k-ary structural primitives — the perfect-subtree decomposition and
//! the generic grouping fold.
//!
//! The structural core is **topology-agnostic**. It names the perfect k-ary
//! subtree decomposition of a log of `n` leaves ([`frontier_for_size`]) and a
//! generic grouping combinator over an arbitrary item list ([`fold_frontier`]),
//! but it does **not** decide how those subtrees are bagged into one root, nor
//! what an inclusion proof points at. Those are *commitment* choices owned by
//! each consumer: the append-only log bags its perfect-subtree peaks into a
//! durable mountain range, the mutable tree folds them into a rebalanced tree —
//! so the concrete topology lives with the structure that owns it, never here.
//!
//! What the core keeps is the **abstract skeleton interface** ([`SkeletonStep`]):
//! the per-step `(position, sibling_count)` shape a consumer's concrete topology
//! emits and the [`crate::proof`] verifier pins a proof against. The verifier
//! *mechanism* lives in [`crate::proof::verify_inclusion`]; the concrete skeleton
//! it checks against is supplied by the consumer, computed once from its own
//! trusted `(tree_size, arity, index)`. Keeping the skeleton as the seam is what
//! lets one verifier serve any topology without the core knowing which.

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

/// A peak-bagging function: fold a structure's frontier peaks (under its own
/// `hasher`, at arity `k`) into one member root.
///
/// The [`Seal`](crate::Seal) stores peaks only and is topology-agnostic; the
/// consumer supplies how they bag — the append-only log's mountain backward-bag,
/// the mutable tree's rebalanced fold. A function pointer (not a closure type) so
/// it threads through the snapshot layer without per-call generics.
pub type BagFn = fn(&dyn crate::Hasher, &[Vec<u8>], u64) -> Vec<u8>;

/// A skeleton provider: compute a structure's concrete inclusion skeleton for
/// `(arity, tree_size, index)`, or `None` for an invalid position.
///
/// The verifier is topology-agnostic; a caller that holds a proof but not the
/// generating structure (a snapshot proof, a coupling verifier) threads this to
/// supply the topology — the append-only log's `mountain_skeleton`, the mutable
/// tree's `rebalanced_skeleton`. A function pointer so it threads without
/// per-call generics.
pub type SkeletonFn = fn(u64, u64, u64) -> Option<Vec<SkeletonStep>>;

/// One step of an inclusion skeleton, ordered leaf → root.
///
/// A consumer's concrete topology emits a sequence of these — one per hashing
/// node on the path from a leaf's perfect-subtree peak up to the structure's
/// root — and the [`crate::proof`] verifier pins a proof's trailing steps
/// against it field by field. The core defines only the interface; which
/// sequence a given structure produces (a mountain range's bag path, a
/// rebalanced tree's grouping path) is the consumer's.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SkeletonStep {
    /// Position of the path node among its parent's children (0-indexed).
    pub position: usize,
    /// Number of sibling digests at this step (children count minus one).
    ///
    /// Always `>= 1`: uniform steps inside a frontier subtree carry `k - 1`
    /// siblings, and a bagging/grouping node has `2..=k` children. A skeleton
    /// therefore never contains a zero-sibling (promoted) step — see the
    /// canonical proof encoding in [`crate::proof`].
    pub sibling_count: usize,
}
