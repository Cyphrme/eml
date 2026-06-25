//! The structural count is the **reduced** count (GLOSSARY: the two-count model).
//!
//! The motivating premise of the Fork B model: general same-value **collapse is
//! structural** — a collapsed run reduces to one node and is *not counted* — and
//! the same holds for **promotion**. So the structural root and the structural
//! geometry a [`spine::Seal`] commits reflect the **canonical (reduced) form**,
//! never pre-collapse multiplicity. The *only* counted quantity in the whole
//! stack — the null-run-extent (the logical count) — belongs to the `polydigest`
//! combinator and is **absent below it**: the structural core (`spine`) names no
//! logical/null count.
//!
//! These are spine-level properties of the canonicalization primitives
//! (`nary_mr`, `evaluate`) and the structural snapshot (`Seal`). They sit one
//! level below CML/CMT and hold for every tier built on the spine.

use sha2::{Digest, Sha256};
use spine::{Hasher, Seal, Subtree, evaluate, frontier_for_size, nary_mr};

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

/// **General same-value collapse reduces the count.** A run of `N` equal
/// children folds to the single value — the structural root is that value, and
/// the multiplicity `N` is *not* in the digest. The root a verifier reconstructs
/// is the reduced one, for every run width and for every value (null is just one
/// such value, never a special case).
#[test]
fn collapse_root_is_the_reduced_value_not_the_multiplicity() {
    let hasher = Sha256Hasher;
    let v = hasher.leaf(b"same");

    // The reduced root of any same-value run is the single value, regardless of
    // how many leaves the run spans. The structural root carries no count.
    let runs: Vec<Vec<&[u8]>> = vec![
        vec![&v],
        vec![&v, &v],
        vec![&v, &v, &v],
        vec![&v, &v, &v, &v, &v, &v, &v],
    ];
    for run in &runs {
        assert_eq!(
            nary_mr(&hasher, run),
            v,
            "a same-value run of width {} must reduce to the single value",
            run.len()
        );
    }

    // Two runs of the *same* value but different multiplicity are
    // byte-identical at the structural root: the count is genuinely absent, not
    // merely small. Distinguishing them is the logical (polydigest) layer's job via
    // the run-extent, never the structural digest's.
    let root_two = nary_mr(&hasher, &[&v, &v]);
    let root_seven = nary_mr(&hasher, &[&v, &v, &v, &v, &v, &v, &v]);
    assert_eq!(
        root_two, root_seven,
        "the structural root must not encode pre-collapse multiplicity"
    );

    // The null collapse is exactly the same rule at `value = null()` — null is a
    // value, not a tracked status. An all-null run reduces to null.
    let null = hasher.null();
    assert_eq!(nary_mr(&hasher, &[&null, &null, &null]), null);

    // A genuinely mixed node does NOT collapse — reduction fires only where
    // there is something to reduce, so distinct values still hash.
    let w = hasher.leaf(b"other");
    assert_eq!(nary_mr(&hasher, &[&v, &w]), hasher.node(&[&v, &w]));
    assert_ne!(nary_mr(&hasher, &[&v, &w]), v);
}

/// **Promotion reduces too.** A lone-child chain of any depth folds to the
/// child: the wrapping nodes are lifted away, contributing no structure to the
/// root. Like collapse, promotion is not counted — the nesting depth is absent
/// from the reduced digest.
#[test]
fn promotion_root_is_the_lone_child_not_the_nesting_depth() {
    let hasher = Sha256Hasher;
    let leaf = hasher.leaf(b"x");

    // Node([Node([Node([Leaf("x")])])]) — three layers of single-child nesting.
    let nested = Subtree::Node(vec![Subtree::Node(vec![Subtree::Node(vec![
        Subtree::Leaf(b"x".to_vec()),
    ])])]);
    // A single bare leaf — zero nesting.
    let bare = Subtree::Leaf(b"x".to_vec());

    // Both reduce to the same leaf hash: promotion erases the nesting depth from
    // the root, exactly as collapse erases run multiplicity.
    assert_eq!(evaluate(&hasher, &nested), leaf);
    assert_eq!(evaluate(&hasher, &bare), leaf);
    assert_eq!(evaluate(&hasher, &nested), evaluate(&hasher, &bare));
}

/// **The structural root reflects the canonical form, end to end.** A subtree
/// whose shape mixes a same-value collapse and a promotion evaluates to the same
/// root as the directly-constructed reduced tree built over only the surviving
/// distinct values. The pre-reduction shape (and the multiplicities within it)
/// leaves no trace in the structural commitment.
#[test]
fn structural_root_equals_the_canonical_reduced_tree() {
    let hasher = Sha256Hasher;

    // Pre-reduction shape: a 3-wide same-value run "a","a","a" beside a
    // single-child-nested "b". Collapse reduces the run to leaf("a"); promotion
    // reduces the nested "b" to leaf("b").
    let pre_reduction = Subtree::Node(vec![
        Subtree::Node(vec![
            Subtree::Leaf(b"a".to_vec()),
            Subtree::Leaf(b"a".to_vec()),
            Subtree::Leaf(b"a".to_vec()),
        ]),
        Subtree::Node(vec![Subtree::Leaf(b"b".to_vec())]),
    ]);

    // The canonical reduced tree: just the two surviving distinct leaves.
    let canonical = Subtree::Node(vec![
        Subtree::Leaf(b"a".to_vec()),
        Subtree::Leaf(b"b".to_vec()),
    ]);

    assert_eq!(
        evaluate(&hasher, &pre_reduction),
        evaluate(&hasher, &canonical),
        "the structural root must equal the canonical reduced form"
    );
}

/// **The structural layer tracks no logical/null count.** The only geometry a
/// `spine::Seal` exposes is the *collapse-frontier* run-extent, derived purely
/// from `(tree_size, arity)` — it is structural shape, not a per-tree null
/// count. A `Seal` built from the same frontier under two different sizes yields
/// run-extents fixed by geometry alone; nothing in the structural snapshot
/// records how many *null* (logically-inactive) leaves a run absorbed. That
/// logical count is the `polydigest` combinator's null-run-extent, and it has no home
/// here.
#[test]
fn seal_run_extents_are_geometry_not_a_logical_count() {
    // The structural run-extent set equals the height >= 1 frontier geometry of
    // (tree_size, arity) — independent of any leaf value, so it cannot be a
    // count of nulls (which are value-dependent and per-tree-divergent).
    let arity = 2u64;
    for size in 1u64..16 {
        let geometry: Vec<(u64, u32)> = frontier_for_size(size, arity)
            .into_iter()
            .filter(|&(_, height)| height >= 1)
            .collect();

        // Build a Seal over an arbitrary single algorithm; its run_extents must
        // match the pure geometry exactly. A peak's *value* never enters, so the
        // run-extent cannot be carrying a null count.
        let peaks: Vec<Vec<u8>> = frontier_for_size(size, arity)
            .iter()
            .map(|&(left, height)| {
                // Any deterministic filler; the extent is value-independent.
                Sha256::digest(format!("{left}:{height}").as_bytes()).to_vec()
            })
            .collect();
        let seal = Seal::new(size, arity, vec![(0u64, peaks)]).expect("well-formed frontier");

        let extents: Vec<(u64, u32)> = seal
            .run_extents()
            .into_iter()
            .map(|e| (e.left(), e.height()))
            .collect();
        assert_eq!(
            extents, geometry,
            "Seal run-extents must be the (size, arity) collapse geometry, not a per-tree null \
             count (size = {size})"
        );
    }
}
