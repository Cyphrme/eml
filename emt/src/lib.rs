//! `emt` — the Epoch Merkle Tree, the **mutable** engineering library over the
//! [`pmt`] kernel.
//!
//! EMT is the mutable peer of the append-only EML library: both are built on
//! the kernel and neither depends on the other (the seal currency between them
//! is [`pmt::Sealed`]). Where EML optimizes an append-only frontier and proves
//! consistency, EMT lets interior cells change — so it keeps **no frontier and
//! no consistency proofs** (the frontier's left-subtrees-sealed assumption is
//! unsound under mutation). It is positional and dense, sharing the kernel's
//! proof-spine index space, and supports:
//!
//! - construct, [`Emt::set`] / [`Emt::get`];
//! - inclusion proofs and **non-membership** (inclusion of the kernel null constant via collapse);
//! - **per-node multi-hash** — a cell addressable under many algorithms — with **retroactive
//!   per-node algorithm addition** at `O(log n)` ([`Emt::add_algorithm_at`]), distinct from bulk
//!   filling (an EML operator);
//! - a one-way [`Emt::seal`] into [`pmt::Sealed`] (no `unseal`).
//!
//! Verification stays in the kernel: a proof generated here is checked with
//! [`pmt::verify_inclusion`] against an authenticated `(index, tree_size,
//! arity, root)`.

mod error;
mod proof;
mod spine;
mod tree;

pub use error::{Error, Result};
// The kernel hasher seam and the proof/seal types the public surface returns
// are re-exported so callers need not also name `pmt` directly.
// Mirrors the re-export symmetry in eml-log (eml/src/lib.rs).
pub use pmt::{Hasher, LeafProof, ProofStep, Sealed, verify_inclusion};
pub use tree::{Config, Emt};

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;

    #[derive(Debug)]
    struct Sha256Hasher;

    impl pmt::Hasher for Sha256Hasher {
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

        fn clone_box(&self) -> Box<dyn pmt::Hasher> {
            Box::new(Sha256Hasher)
        }
    }

    const ALG: u64 = 0;
    const K: u64 = 2;

    fn tree_with(payloads: &[&[u8]]) -> Emt {
        let mut t = Emt::new(Config { arity: K }).expect("valid arity");
        t.register_algorithm(ALG, Box::new(Sha256Hasher))
            .expect("fresh alg");
        for (i, p) in payloads.iter().enumerate() {
            t.set(i as u64, p.to_vec(), Vec::new()).expect("dense set");
        }
        t
    }

    #[test]
    fn empty_tree_has_no_root() {
        let t = Emt::new(Config::default()).unwrap();
        assert!(t.is_empty());
        assert_eq!(t.root(ALG), None);
    }

    #[test]
    fn rejects_out_of_range_arity() {
        assert_eq!(
            Emt::new(Config { arity: 1 }).unwrap_err(),
            Error::InvalidArity(1)
        );
        assert_eq!(
            Emt::new(Config { arity: 257 }).unwrap_err(),
            Error::InvalidArity(257)
        );
    }

    #[test]
    fn set_get_round_trips_and_overwrites() {
        let mut t = tree_with(&[b"a", b"b", b"c"]);
        assert_eq!(t.get(1), Some(b"b".as_slice()));
        t.set(1, b"B".to_vec(), Vec::new()).unwrap();
        assert_eq!(t.get(1), Some(b"B".as_slice()));
        assert_eq!(t.len(), 3);
    }

    #[test]
    fn set_rejects_a_gap() {
        let mut t = tree_with(&[b"a"]);
        assert_eq!(
            t.set(5, b"x".to_vec(), Vec::new()).unwrap_err(),
            Error::IndexGap { index: 5, len: 1 }
        );
    }

    #[test]
    fn metadata_is_carried_verbatim_and_uninterpreted() {
        let mut t = tree_with(&[b"a"]);
        let meta = vec![0xDE, 0xAD, 0xBE, 0xEF];
        t.set(0, b"a".to_vec(), meta.clone()).unwrap();
        assert_eq!(t.metadata(0), Some(meta.as_slice()));
        // Metadata never feeds the digest: same payload, different metadata,
        // same root.
        let r_with_meta = t.root(ALG).unwrap();
        let mut t2 = tree_with(&[b"a"]);
        t2.set(0, b"a".to_vec(), vec![0x00]).unwrap();
        assert_eq!(t2.root(ALG).unwrap(), r_with_meta);
    }

    /// The materialized root equals a from-scratch kernel evaluation of the
    /// canonical subtree — the oracle pinning the spine to PMT semantics.
    #[test]
    fn root_matches_kernel_evaluate() {
        for size in 1u64..=20 {
            let payloads: Vec<Vec<u8>> = (0..size).map(|i| format!("p{i}").into_bytes()).collect();
            let refs: Vec<&[u8]> = payloads.iter().map(Vec::as_slice).collect();
            let t = tree_with(&refs);
            let expected = kernel_root(&payloads);
            assert_eq!(t.root(ALG).unwrap(), expected, "size={size}");
        }
    }

    /// Build the canonical kernel subtree for a flat sequence at k=2 and
    /// evaluate it, independent of EMT's materialization.
    fn kernel_root(payloads: &[Vec<u8>]) -> Vec<u8> {
        use pmt::Subtree;
        use pmt::topology::frontier_for_size;
        let h = Sha256Hasher;
        let leaves: Vec<Subtree> = payloads.iter().map(|p| Subtree::Leaf(p.clone())).collect();
        // Reassemble the same frontier-folded shape the kernel topology uses.
        let coords = frontier_for_size(payloads.len() as u64, K);
        let mut frontier: Vec<Subtree> = coords
            .iter()
            .map(|&(left, height)| perfect(&leaves, left, height))
            .collect();
        let k = K as usize;
        while frontier.len() > k {
            let split = frontier.len() - k;
            let group = frontier.split_off(split);
            frontier.push(Subtree::Node(group));
        }
        let shape = if frontier.len() == 1 {
            frontier.pop().unwrap()
        } else {
            Subtree::Node(frontier)
        };
        pmt::evaluate(&h, &shape)
    }

    fn perfect(leaves: &[pmt::Subtree], left: u64, height: u32) -> pmt::Subtree {
        use pmt::Subtree;
        if height == 0 {
            return leaves[left as usize].clone();
        }
        let span = K.pow(height - 1);
        let children = (0..K)
            .map(|c| perfect(leaves, left + c * span, height - 1))
            .collect();
        Subtree::Node(children)
    }

    #[test]
    fn inclusion_proof_verifies_against_kernel() {
        for size in 1u64..=20 {
            let payloads: Vec<Vec<u8>> = (0..size).map(|i| format!("v{i}").into_bytes()).collect();
            let refs: Vec<&[u8]> = payloads.iter().map(Vec::as_slice).collect();
            let t = tree_with(&refs);
            let root = t.root(ALG).unwrap();
            let h = Sha256Hasher;
            for index in 0..size {
                let (leaf, path) = t.inclusion_proof(ALG, index).unwrap();
                assert!(
                    pmt::verify_inclusion(&h, &leaf, index, size, K, &path, &root),
                    "size={size} index={index}"
                );
            }
        }
    }

    /// F4 regression guard: off-path siblings are served from the materialized
    /// cache, not re-evaluated. A fully materialized tree must generate inclusion
    /// proofs with zero cache misses for every index. A positive miss count means
    /// the cache is being bypassed and proof generation has silently degraded to
    /// O(n) rather than O(log n).
    #[test]
    fn inclusion_proof_uses_cache_zero_misses() {
        // Use a reasonably large tree (size > k^2) so there are genuine inner
        // nodes with off-path siblings that would trigger misses without caching.
        let size = 32u64;
        let payloads: Vec<Vec<u8>> = (0..size).map(|i| format!("p{i}").into_bytes()).collect();
        let refs: Vec<&[u8]> = payloads.iter().map(Vec::as_slice).collect();
        let t = tree_with(&refs);
        for index in 0..size {
            let (_, _, misses) = t
                .inclusion_proof_miss_count(ALG, index)
                .expect("in-range index");
            assert_eq!(
                misses, 0,
                "inclusion_proof for index={index} size={size} had {misses} cache miss(es): \
                 off-path siblings must be served from the materialized cache (F4)"
            );
        }
    }

    #[test]
    fn inclusion_proof_rejects_wrong_leaf() {
        let t = tree_with(&[b"a", b"b", b"c", b"d"]);
        let root = t.root(ALG).unwrap();
        let h = Sha256Hasher;
        let (_, path) = t.inclusion_proof(ALG, 2).unwrap();
        let forged = h.leaf(b"not-c");
        assert!(!pmt::verify_inclusion(&h, &forged, 2, 4, K, &path, &root));
    }

    #[test]
    fn non_membership_of_a_null_cell_verifies() {
        // A cell explicitly set to the null preimage hashes to null(); its
        // non-membership (inclusion-of-null) proof verifies.
        let h = Sha256Hasher;
        let mut t = tree_with(&[b"real", b"x", b"y"]);
        t.set(1, b"null".to_vec(), Vec::new()).unwrap();
        let root = t.root(ALG).unwrap();
        let (leaf, path) = t.non_membership_proof(ALG, 1).expect("cell hashes to null");
        assert_eq!(leaf, h.null());
        assert!(pmt::verify_inclusion(
            &h,
            &leaf,
            1,
            t.len(),
            K,
            &path,
            &root
        ));
        // A present (non-null) cell has no non-membership proof.
        assert_eq!(t.non_membership_proof(ALG, 0), None);
    }

    #[test]
    fn leaf_proof_accepts_legit_and_rejects_forged() {
        let h = Sha256Hasher;
        for size in 1u64..=20 {
            let payloads: Vec<Vec<u8>> = (0..size).map(|i| format!("v{i}").into_bytes()).collect();
            let refs: Vec<&[u8]> = payloads.iter().map(Vec::as_slice).collect();
            let t = tree_with(&refs);
            let root = t.root(ALG).unwrap();
            for index in 0..size {
                let proof = t.leaf_proof(ALG, index).expect("in range");
                // Legitimate leaf accepted.
                assert!(proof.verify(&h, &root), "size={size} index={index}");
                // Forged leaf at the same position rejected.
                let mut forged = proof.clone();
                forged.leaf_hash = h.leaf(b"forged");
                assert!(!forged.verify(&h, &root), "size={size} index={index}");
            }
        }
        // Out-of-range and unknown-algorithm produce no proof.
        let t = tree_with(&[b"a", b"b"]);
        assert!(t.leaf_proof(ALG, 2).is_none());
        assert!(t.leaf_proof(99, 0).is_none());
    }

    #[test]
    fn seal_is_one_way_into_kernel_sealed() {
        let t = tree_with(&[b"a", b"b", b"c"]);
        let root = t.root(ALG).unwrap();
        let sealed = t.seal().expect("non-empty seal");
        assert_eq!(sealed.tree_size(), 3);
        assert_eq!(sealed.arity(), 2);
        // The seal computed the resumable frontier; folding its peaks under the
        // algorithm's own hash reproduces the live root.
        assert!(sealed.peaks(ALG).is_some());
        assert_eq!(sealed.member_root(ALG, &Sha256Hasher), Some(root));
        // `sealed` is a kernel value; there is no path back to an `Emt`.
    }

    #[test]
    fn empty_tree_cannot_be_sealed() {
        let t = Emt::new(Config::default()).unwrap();
        assert_eq!(t.seal().unwrap_err(), Error::EmptySeal);
    }
}
