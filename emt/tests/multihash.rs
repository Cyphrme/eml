//! Property tests for the EMT's two cost classes (CN6-MULTIHASH, D11):
//!
//! - **incremental** (this crate): a node gains a digest under a new algorithm, the root recomputed
//!   in `O(log n)` along its ancestors only; and
//! - the path-recompute on `set` agrees with a from-scratch rebuild.
//!
//! The incremental add is shown *distinct* from a from-scratch (`O(n)`) build:
//! it yields the identical root while touching only the ancestor path, witnessed
//! by the recompute count being the path depth rather than the node total.

use emt::{Config, Emt, Hasher};
use proptest::prelude::*;
use sha2::{Digest, Sha256};

#[derive(Debug, Clone, Copy)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for c in children {
            h.update(c);
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
        Box::new(*self)
    }
}

/// A second, distinct hash so a from-scratch build under the *new* algorithm is
/// observably different from the first algorithm's tree.
#[derive(Debug, Clone, Copy)]
struct DoubleSha;

impl Hasher for DoubleSha {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(Sha256::digest(data)).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for c in children {
            h.update(c);
        }
        Sha256::digest(h.finalize()).to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(Sha256::digest(b"")).to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(Sha256::digest(data)).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(*self)
    }
}

const ALG0: u64 = 0;
const ALG1: u64 = 1;
const K: u64 = 2;

fn build(payloads: &[Vec<u8>]) -> Emt {
    let mut t = Emt::new(Config { arity: K }).unwrap();
    t.register_algorithm(ALG0, Box::new(Sha256Hasher)).unwrap();
    for (i, p) in payloads.iter().enumerate() {
        t.set(i as u64, p.clone(), Vec::new()).unwrap();
    }
    t
}

/// `ceil(log_k(size))` — the maximum ancestor depth of any cell, the `O(log n)`
/// bound the per-node recompute must stay within.
fn max_depth(size: u64, k: u64) -> usize {
    let mut depth = 0usize;
    let mut cap = 1u64;
    while cap < size {
        cap = cap.saturating_mul(k);
        depth += 1;
    }
    depth
}

proptest! {
    /// Retroactive per-node algorithm addition is *correct*: the resulting root
    /// under the new algorithm equals a from-scratch build that hashed only the
    /// target cell under it (every other cell null). It is also *local*: the
    /// recompute count is the target's ancestor depth, never the node total —
    /// the `O(log n)` cost class, distinct from a bulk `O(n)` build.
    #[test]
    fn retroactive_add_is_correct_and_local(
        payloads in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..8), 1..40usize),
        target_frac in 0..1000u64,
    ) {
        let size = payloads.len() as u64;
        let index = target_frac % size;

        let mut t = build(&payloads);
        let recomputed = t.add_algorithm_at(ALG1, index, Box::new(DoubleSha)).unwrap();
        let got = t.root(ALG1).unwrap();

        // Locality: the recompute count is the ancestor depth (O(log n)), and
        // strictly below the cell count for any non-trivial tree.
        prop_assert!(recomputed <= max_depth(size, K), "recomputed={recomputed} size={size}");
        if size > 1 {
            prop_assert!((recomputed as u64) < size, "recompute touched every node");
        }

        // Correctness: a from-scratch tree under DoubleSha where only `index`
        // carries a real payload (the rest null) yields the same root.
        let h = DoubleSha;
        let null = h.null();
        let oracle: Vec<Vec<u8>> = (0..size)
            .map(|i| if i == index { payloads[index as usize].clone() } else { null.clone() })
            .collect();
        let mut scratch = Emt::new(Config { arity: K }).unwrap();
        scratch.register_algorithm(ALG1, Box::new(DoubleSha)).unwrap();
        for (i, p) in oracle.iter().enumerate() {
            // A cell whose payload IS the null preimage hashes to null(), so
            // this reproduces "only `index` hashed under the new algorithm".
            let payload = if i as u64 == index { p.clone() } else { b"null".to_vec() };
            scratch.set(i as u64, payload, Vec::new()).unwrap();
        }
        prop_assert_eq!(got, scratch.root(ALG1).unwrap());
    }

    /// The path-recompute on `set` always agrees with a from-scratch rebuild:
    /// overwriting a cell and rebuilding from the final cell values give the
    /// same root.
    #[test]
    fn set_path_recompute_matches_rebuild(
        initial in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..6), 1..30usize),
        edit_idx in 0..1000u64,
        new_payload in prop::collection::vec(any::<u8>(), 0..6),
    ) {
        let size = initial.len() as u64;
        let index = edit_idx % size;

        let mut t = build(&initial);
        t.set(index, new_payload.clone(), Vec::new()).unwrap();
        let incremental = t.root(ALG0).unwrap();

        let mut final_vals = initial;
        final_vals[index as usize] = new_payload;
        let rebuilt = build(&final_vals).root(ALG0).unwrap();

        prop_assert_eq!(incremental, rebuilt);
    }
}

// ---------------------------------------------------------------------------
// Live combined root: the primary identity of the mutable tree, the
// canonicalization fold over the per-algorithm member roots (trivial coverage).
// ---------------------------------------------------------------------------

/// A single-algorithm tree's combined root IS its member root — native
/// promotion (`nary_mr` len==1), no predicate.
#[test]
fn single_algorithm_combined_root_promotes_to_member_root() {
    for n in 1u64..16 {
        let payloads: Vec<Vec<u8>> = (0..n).map(|i| format!("c{i}").into_bytes()).collect();
        let t = build(&payloads);
        let member = t.root(ALG0).unwrap();
        let combined = t
            .combined_root(ALG0)
            .expect("non-empty tree has a combined root");
        assert_eq!(
            combined, member,
            "single-alg combined root must promote (n={n})"
        );
    }
}

/// A multi-algorithm tree's combined root is the flat `nary_mr` node over the
/// per-algorithm member roots (children in algorithm-ID order). With a trivial
/// timeline there is no coverage child, so under a hasher whose `node` simply
/// concatenates-and-hashes the children, the combined root equals
/// `H(member_root_0 ‖ member_root_1)`.
#[test]
fn multi_algorithm_combined_root_is_the_fold_over_members() {
    let payloads: Vec<Vec<u8>> = (0..5u64).map(|i| format!("c{i}").into_bytes()).collect();
    let mut t = Emt::new(Config { arity: K }).unwrap();
    t.register_algorithm(ALG0, Box::new(Sha256Hasher)).unwrap();
    t.register_algorithm(ALG1, Box::new(DoubleSha)).unwrap();
    for (i, p) in payloads.iter().enumerate() {
        t.set(i as u64, p.clone(), Vec::new()).unwrap();
    }

    let mr0 = t.root(ALG0).unwrap();
    let mr1 = t.root(ALG1).unwrap();

    // The combined root under ALG0's hash folds [mr0, mr1] as two children.
    let combined0 = t.combined_root(ALG0).unwrap();
    let expected0 = Sha256Hasher.node(&[mr0.as_slice(), mr1.as_slice()]);
    assert_eq!(combined0, expected0);

    // Under ALG1's hash the *same* two children fold under the other hasher —
    // each algorithm's combined root rests solely on its own hash (D9).
    let combined1 = t.combined_root(ALG1).unwrap();
    let expected1 = DoubleSha.node(&[mr0.as_slice(), mr1.as_slice()]);
    assert_eq!(combined1, expected1);
    assert_ne!(combined0, combined1);

    // The combined root is a genuine parent, not one of its member children.
    assert_ne!(combined0, mr0);
    assert_ne!(combined0, mr1);
}

/// An empty tree or an unregistered algorithm has no combined root.
#[test]
fn combined_root_is_none_for_empty_or_unregistered() {
    let mut empty = Emt::new(Config { arity: K }).unwrap();
    empty
        .register_algorithm(ALG0, Box::new(Sha256Hasher))
        .unwrap();
    assert_eq!(
        empty.combined_root(ALG0),
        None,
        "empty tree has no combined root"
    );

    let t = build(&[b"a".to_vec()]);
    assert_eq!(
        t.combined_root(99),
        None,
        "unregistered algorithm has no combined root"
    );
}
