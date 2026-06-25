//! The CML structural count is the **reduced** count (GLOSSARY: the two-count
//! model, at the canonical-log layer).
//!
//! CML is single-algorithm and **epoch-free**: it carries one frontier and folds
//! it into a member root. The two-count model says the structural quantity CML
//! commits is the **reduced** fold — same-value collapse and promotion both
//! reduce, and no logical/null count is tracked at this layer. Here we drive the
//! engine's frontier carry directly and assert the member root reflects the
//! canonical (reduced) form, never pre-collapse multiplicity.
//!
//! The complementary structural-primitive properties live one level down in
//! `spine/tests/two_count.rs`; this file exercises them through CML's own
//! frontier engine (`AlgView` + `carry` + `compute_root`).

use cml::{AlgView, Hasher, carry, compute_root};
use sha2::{Digest, Sha256};

#[derive(Debug)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for child in children {
            h.update(child);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(Sha256Hasher)
    }
}

/// Build a fresh single-algorithm view, active from index 0.
fn fresh_view() -> AlgView {
    AlgView {
        hasher: Box::new(Sha256Hasher),
        epochs: vec![(0, u64::MAX)],
        frontier: Vec::new(),
        frontier_coords: Vec::new(),
    }
}

/// Carry `count` leaf digests through the frontier, returning the view.
fn carry_run(digests: &[Vec<u8>], arity: u64) -> AlgView {
    let mut view = fresh_view();
    let mut sink: Vec<(u64, u64, u32, Vec<u8>)> = Vec::new();
    for (i, d) in digests.iter().enumerate() {
        carry::<std::convert::Infallible>(&mut view, 0, d.clone(), i as u64, arity, &mut sink)
            .expect("well-formed carry never underflows");
    }
    view
}

/// **A same-value run collapses to the single value in the CML member root.**
/// Appending `N` identical leaf digests yields a member root equal to that one
/// digest — at every power-of-`k` width where the run fully collapses. The
/// structural root is the reduced value; the multiplicity `N` is absent.
#[test]
fn member_root_of_same_value_run_is_the_single_value() {
    let hasher = Sha256Hasher;
    let arity = 2u64;
    let d = hasher.leaf(b"same");

    // At k = 2, a run whose width is a power of two collapses fully to `d`:
    // every pairwise merge folds two equal children to that value.
    for &width in &[1usize, 2, 4, 8] {
        let run = vec![d.clone(); width];
        let view = carry_run(&run, arity);
        assert_eq!(
            compute_root(&view, arity as usize),
            d,
            "a same-value run of width {width} must reduce to the single value"
        );
    }

    // Two fully-collapsing runs of different width share a byte-identical member
    // root: the structural count is genuinely reduced, not merely small.
    let root_two = compute_root(&carry_run(&vec![d.clone(); 2], arity), arity as usize);
    let root_eight = compute_root(&carry_run(&vec![d.clone(); 8], arity), arity as usize);
    assert_eq!(
        root_two, root_eight,
        "the CML member root must not encode pre-collapse multiplicity"
    );
}

/// **A distinct-value log does NOT collapse — reduction fires only where there
/// is something to reduce.** Two different leaves produce the hashed node root,
/// confirming the same engine that collapses equal runs preserves genuine
/// structure. This pins down that the reduction is value-dependent, not a blanket
/// count-erasure.
#[test]
fn member_root_of_distinct_values_hashes_not_collapses() {
    let hasher = Sha256Hasher;
    let arity = 2u64;
    let a = hasher.leaf(b"a");
    let b = hasher.leaf(b"b");

    let view = carry_run(&[a.clone(), b.clone()], arity);
    let root = compute_root(&view, arity as usize);

    assert_eq!(root, hasher.node(&[&a, &b]));
    assert_ne!(root, a);
    assert_ne!(root, b);
}

/// **The null collapse is the same rule at `value = null()`.** An all-null run
/// reduces to null in the member root — null is one collapsing *value*, carrying
/// no special status at the CML (structural) layer. The *count* of nulls (the
/// logical null-run-extent) is the `epoch` combinator's concern; CML records
/// none of it.
#[test]
fn member_root_of_null_run_is_null_no_count_tracked() {
    let hasher = Sha256Hasher;
    let arity = 2u64;
    let null = hasher.null();

    for &width in &[1usize, 2, 4] {
        let run = vec![null.clone(); width];
        let view = carry_run(&run, arity);
        assert_eq!(
            compute_root(&view, arity as usize),
            null,
            "an all-null run of width {width} reduces to null at the CML layer"
        );
    }
}
