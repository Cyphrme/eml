//! Leaf proof — a first-class, live "is this a legitimate leaf?" witness.
//!
//! The leaf proof is the **peer of the inclusion proof** ([`crate::proof`]) over
//! the *same* shared positional topology ([`crate::topology`]): where a raw
//! [`verify_inclusion`](crate::proof::verify_inclusion) call binds a leaf to a
//! log position from seven loose parameters, a [`LeafProof`] packages the leaf
//! hash and its trusted positional parameters into one self-contained value, so
//! a consumer asks a single question — `verify(hasher, root)` — against an
//! authenticated root.
//!
//! It runs over a **live** tree (both the append-only EML and the mutable EMT
//! expose it), and is **not** consistency-coupled: a tree that proves no
//! consistency still answers "legitimate leaf?". It is the base case the
//! snapshot proof composes.
//!
//! # Trust contract (security-critical)
//!
//! A `LeafProof` carries `index`, `tree_size`, and `log_arity` — these are
//! **trusted positional parameters**, inherited verbatim from the inclusion
//! contract ([`verify_inclusion`](crate::proof::verify_inclusion)). They pin the
//! topology the verifier reconstructs and MUST come from an authenticated source
//! (a signed Tree Head or trusted checkpoint), never from caller-untrusted
//! input. The `root` passed to [`LeafProof::verify`] must likewise be
//! authenticated for that `tree_size`. A `true` result binds `leaf_hash` to log
//! position `index` only — payload activity is read from the committed epoch
//! timeline, never inferred here.

use crate::hasher::Hasher;
use crate::proof::{ProofStep, verify_inclusion};

/// A self-contained leaf proof: a leaf hash bound to its log position, ready to
/// verify against a trusted root.
///
/// The path and positional fields are exactly the inclusion contract; bundling
/// them is what makes the proof self-describing — `verify` needs only the hasher
/// and the trusted root, not a re-supply of `(index, tree_size, log_arity)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeafProof {
    /// The proven leaf's digest at `index`.
    pub leaf_hash: Vec<u8>,
    /// Trusted log position of the leaf (0-indexed).
    pub index: u64,
    /// Trusted size of the tree the proof is rooted in.
    pub tree_size: u64,
    /// Trusted fixed arity of the proof spine (`2..=256`).
    pub log_arity: u64,
    /// Path steps from the leaf to the root, over the shared positional
    /// topology — the same shape [`verify_inclusion`] reconstructs against.
    pub path: Vec<ProofStep>,
}

impl LeafProof {
    /// Assemble a leaf proof from a leaf hash and its trusted positional
    /// parameters plus an inclusion path.
    ///
    /// This is the kernel-level producer the engineering libraries (EML, EMT)
    /// wrap around their own path generation; they own the live-tree walk, the
    /// kernel owns the self-contained witness shape.
    #[must_use]
    pub fn new(
        leaf_hash: Vec<u8>,
        index: u64,
        tree_size: u64,
        log_arity: u64,
        path: Vec<ProofStep>,
    ) -> Self {
        Self {
            leaf_hash,
            index,
            tree_size,
            log_arity,
            path,
        }
    }

    /// Verify the leaf proof against an authenticated `root`: is `leaf_hash` the
    /// legitimate leaf at `index` in the size-`tree_size` tree rooted at `root`?
    ///
    /// Soundness rests entirely on the topology the verifier reconstructs from
    /// the trusted `(index, tree_size, log_arity)`; the proof supplies only
    /// sibling digests. See the module-level trust contract — `root` and the
    /// positional fields MUST be authenticated.
    #[must_use]
    pub fn verify(&self, hasher: &dyn Hasher, root: &[u8]) -> bool {
        verify_inclusion(
            hasher,
            &self.leaf_hash,
            self.index,
            self.tree_size,
            self.log_arity,
            &self.path,
            root,
        )
    }
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;
    use crate::mr::within_subtree_path;
    use crate::subtree::Subtree;

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

    /// A balanced binary subtree over `n` leaves `0..n`, mirroring the canonical
    /// k=2 frontier shape a flat log of that size produces. Used as an in-test
    /// live tree so the kernel leaf proof can be exercised without an engineering
    /// crate.
    fn balanced(n: u64) -> Subtree {
        fn build(lo: u64, hi: u64) -> Subtree {
            if hi - lo == 1 {
                return Subtree::Leaf(format!("leaf-{lo}").into_bytes());
            }
            // Largest power-of-two strictly below the span, matching the k=2
            // frontier's leftmost-perfect split.
            let span = hi - lo;
            let mut left_span = 1;
            while left_span * 2 < span {
                left_span *= 2;
            }
            Subtree::Node(vec![build(lo, lo + left_span), build(lo + left_span, hi)])
        }
        build(0, n)
    }

    /// Produce a leaf proof for `index` over the balanced k=2 tree of size `n`,
    /// using the kernel's own subtree-path generator.
    fn proof_for(hasher: &dyn Hasher, n: u64, index: u64) -> (LeafProof, Vec<u8>) {
        let tree = balanced(n);
        let root = crate::mr::evaluate(hasher, &tree);
        let path = within_subtree_path(hasher, &tree, index).expect("index in range");
        let leaf_hash = hasher.leaf(format!("leaf-{index}").into_bytes().as_slice());
        (LeafProof::new(leaf_hash, index, n, 2, path), root)
    }

    /// Spec: a legitimate leaf's proof verifies against the genuine root, at
    /// every position of every tree size in the swept range.
    #[test]
    fn legitimate_leaf_is_accepted() {
        let hasher = Sha256Hasher;
        for n in 1u64..=33 {
            let tree = balanced(n);
            let root = crate::mr::evaluate(&hasher, &tree);
            for index in 0..n {
                let (proof, root2) = proof_for(&hasher, n, index);
                assert_eq!(root2, root, "n={n} index={index}");
                assert!(proof.verify(&hasher, &root), "n={n} index={index}");
            }
        }
    }

    /// Spec: a forged leaf (wrong payload at the proven position) is rejected.
    #[test]
    fn forged_leaf_is_rejected() {
        let hasher = Sha256Hasher;
        for n in 2u64..=33 {
            for index in 0..n {
                let (mut proof, root) = proof_for(&hasher, n, index);
                proof.leaf_hash = hasher.leaf(b"forged-payload");
                assert!(!proof.verify(&hasher, &root), "n={n} index={index}");
            }
        }
    }

    /// Property: a proof for one position never verifies a leaf hash bound to a
    /// *different* position's payload (the path pins the position).
    #[test]
    fn proof_does_not_transfer_across_positions() {
        let hasher = Sha256Hasher;
        let n = 16;
        for index in 0..n {
            let (mut proof, root) = proof_for(&hasher, n, index);
            for other in 0..n {
                if other == index {
                    continue;
                }
                proof.leaf_hash = hasher.leaf(format!("leaf-{other}").into_bytes().as_slice());
                assert!(!proof.verify(&hasher, &root), "index={index} other={other}");
            }
            // Restore: the genuine leaf still verifies.
            proof.leaf_hash = hasher.leaf(format!("leaf-{index}").into_bytes().as_slice());
            assert!(proof.verify(&hasher, &root), "index={index}");
        }
    }

    /// Property: a proof never verifies against the root of a genuinely
    /// different tree (wrong-root rejection), nor under a mismatched trusted
    /// `tree_size`.
    #[test]
    fn wrong_root_or_size_is_rejected() {
        let hasher = Sha256Hasher;
        let (proof, root) = proof_for(&hasher, 8, 3);
        // A different tree (different size) has a different root.
        let other_root = crate::mr::evaluate(&hasher, &balanced(12));
        assert_ne!(root, other_root);
        assert!(proof.verify(&hasher, &root));
        assert!(!proof.verify(&hasher, &other_root));

        // Mismatched trusted tree_size reconstructs a different topology.
        let mut wrong_size = proof.clone();
        wrong_size.tree_size = 9;
        assert!(!wrong_size.verify(&hasher, &root));
    }

    /// The leaf proof is exactly the inclusion contract repackaged: its `verify`
    /// agrees with a direct `verify_inclusion` call on the same parameters.
    #[test]
    fn verify_agrees_with_raw_inclusion() {
        let hasher = Sha256Hasher;
        let (proof, root) = proof_for(&hasher, 11, 7);
        let direct = verify_inclusion(
            &hasher,
            &proof.leaf_hash,
            proof.index,
            proof.tree_size,
            proof.log_arity,
            &proof.path,
            &root,
        );
        assert_eq!(proof.verify(&hasher, &root), direct);
        assert!(direct);
    }
}
