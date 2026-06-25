//! `polydigest(cmt)` binding-view tests — the combined root over the mutable tree's
//! per-algorithm member roots (D9/D12).
//!
//! The structural per-algorithm roots and the multi-hash materialization are the
//! CMT's (tested in `cmt`); this combinator folds them into the binding /
//! combined root under the mutable tree's trivial active-from-genesis timeline,
//! so there is no coverage child and the fold is the plain canonicalization fold
//! over the member roots. These tests pin that fold and the combined-currency
//! seal of `polydigest(cmt)`.

use polydigest::{CmtConfig, EpochTree, Hasher};
use sha2::{Digest, Sha256};

#[derive(Debug, Clone, Copy)]
struct Sha256Hasher;

impl polydigest::Hasher for Sha256Hasher {
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

    fn clone_box(&self) -> Box<dyn polydigest::Hasher> {
        Box::new(*self)
    }
}

/// A second, distinct hash so each algorithm's tree (and its combined root) is
/// observably different.
#[derive(Debug, Clone, Copy)]
struct DoubleSha;

impl polydigest::Hasher for DoubleSha {
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

    fn clone_box(&self) -> Box<dyn polydigest::Hasher> {
        Box::new(*self)
    }
}

const ALG0: u64 = 0;
const ALG1: u64 = 1;
const K: u64 = 2;

fn tree_with(payloads: &[Vec<u8>]) -> EpochTree {
    let mut t = EpochTree::new(CmtConfig { arity: K }).unwrap();
    t.register_algorithm(ALG0, Box::new(Sha256Hasher)).unwrap();
    for (i, p) in payloads.iter().enumerate() {
        t.set(i as u64, p.clone(), Vec::new()).unwrap();
    }
    t
}

/// A single-algorithm tree's combined root IS its member root — native
/// promotion (`nary_mr` len==1), no predicate.
#[test]
fn single_algorithm_combined_root_promotes_to_member_root() {
    for n in 1u64..16 {
        let payloads: Vec<Vec<u8>> = (0..n).map(|i| format!("c{i}").into_bytes()).collect();
        let t = tree_with(&payloads);
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
    let mut t = EpochTree::new(CmtConfig { arity: K }).unwrap();
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
    let mut empty = EpochTree::new(CmtConfig { arity: K }).unwrap();
    empty
        .register_algorithm(ALG0, Box::new(Sha256Hasher))
        .unwrap();
    assert_eq!(
        empty.combined_root(ALG0),
        None,
        "empty tree has no combined root"
    );

    let t = tree_with(&[b"a".to_vec()]);
    assert_eq!(
        t.combined_root(99),
        None,
        "unregistered algorithm has no combined root"
    );
}

/// The seal of `polydigest(cmt)` is the combined currency `Sealed`: the structural
/// frontier paired with the trivial timeline, deriving the same member root the
/// live tree carries, and a binding root.
#[test]
fn seal_yields_combined_currency_with_derived_roots() {
    let payloads: Vec<Vec<u8>> = (0..3u64).map(|i| format!("s{i}").into_bytes()).collect();
    let t = tree_with(&payloads);
    let live_member = t.root(ALG0).unwrap();

    let sealed = t.seal().unwrap();
    assert_eq!(sealed.tree_size(), 3);
    assert_eq!(sealed.arity(), K);
    // The sealed member root (the mutable tree's rebalanced fold of the frontier
    // peaks) equals the live root.
    assert_eq!(
        sealed.member_root(ALG0, &Sha256Hasher, polydigest::rebalanced_bag),
        Some(live_member)
    );
    // The binding root for the lone algorithm is derived on demand.
    let hashers: [(u64, &dyn polydigest::Hasher); 1] = [(ALG0, &Sha256Hasher)];
    assert!(
        sealed
            .binding_root(ALG0, &Sha256Hasher, &hashers, polydigest::rebalanced_bag)
            .unwrap()
            .is_some()
    );
}
