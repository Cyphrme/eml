//! Property tests for the CMT's structural multi-hash cost classes (CN6-MULTIHASH, D11):
//!
//! - **incremental**: a node gains a digest under a new algorithm, the root recomputed in `O(log
//!   n)` along its ancestors only; and
//! - the path-recompute on `set` agrees with a from-scratch rebuild.
//!
//! The incremental add is shown *distinct* from a from-scratch (`O(n)`) build:
//! it yields the identical root while touching only the ancestor path, witnessed
//! by the recompute count being the path depth rather than the node total.
//!
//! The binding / combined root over these per-algorithm member roots is the
//! `polydigest` combinator's facet, not the CMT's — its tests live in `polydigest`.

use cmt::{Cmt, Config, Hasher};
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

fn build(payloads: &[Vec<u8>]) -> Cmt {
    let mut t = Cmt::new(Config { arity: K }).unwrap();
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
        let mut scratch = Cmt::new(Config { arity: K }).unwrap();
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
