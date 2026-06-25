//! `spine` — the Merkle Spine: the structural core.
//!
//! The structural engine shared by every tree built above it, **epoch-free** and
//! **topology-agnostic**: **canonicalization** (collapse + promotion, in [`mr`]),
//! the perfect-subtree **decomposition** and grouping combinator ([`topology`]),
//! the [`Hasher`] seam, the **abstract inclusion verifier** (proof pinned against
//! a consumer-supplied skeleton, in [`proof`]), the [`LeafProof`], the general
//! structural [`Seal`] (peak storage), and the opaque **metadata channel**
//! ([`Meta`]). It depends on nothing.
//!
//! The spine carries no **commitment topology**: how perfect subtrees are bagged
//! into one root, and what an inclusion proof points at, are owned by each
//! consumer (the append-only log's mountain range; the mutable tree's rebalanced
//! fold). The seam between them is the [`SkeletonStep`] interface — the consumer
//! computes its concrete skeleton, the spine verifier pins a proof against it.
//!
//! Activation, the committed epoch timeline, the null-run-extents, the binding
//! root, and coupling are **not** here — they are the `polydigest` combinator's
//! facet, which lifts this structural engine across N algorithms over one
//! shared data substrate. The spine names no epoch concept.

pub mod hasher;
pub mod mr;
pub mod proof;
pub mod subtree;
pub mod topology;

pub(crate) mod error;
pub(crate) mod leaf_proof;
pub(crate) mod metadata;
pub(crate) mod seal;

pub use error::{Error, Result};
pub use hasher::Hasher;
pub use leaf_proof::LeafProof;
pub use metadata::Meta;
pub use mr::{count_leaves, evaluate, nary_mr, within_subtree_path};
pub use proof::{
    InclusionProof, ProofStep, constant_time_eq, reconstruct_inclusion_root, verify_inclusion,
    verify_inclusion_path_structure,
};
pub use seal::{RunExtent, Seal};
pub use subtree::Subtree;
pub use topology::{
    ARITY_RANGE, BagFn, SkeletonFn, SkeletonStep, fold_frontier, frontier_for_size,
};

/// Dynamically generate a null digest constant using the hasher.
#[must_use]
pub fn null_digest(hasher: &dyn Hasher) -> Vec<u8> {
    hasher.hash(b"null")
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;
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

    /// A child-tree root carried as `Subtree::Leaf` is indistinguishable from
    /// a raw-payload leaf carrying the same bytes — the opacity contract.
    /// The spine sees identical structure regardless of origin.
    #[test]
    fn leaf_carrying_child_root_is_opaque() {
        let hasher = Sha256Hasher;
        let child_root = evaluate(
            &hasher,
            &Subtree::Node(vec![
                Subtree::Leaf(b"a".to_vec()),
                Subtree::Leaf(b"b".to_vec()),
            ]),
        );

        // A leaf wrapping a child root is structurally identical to a raw-payload
        // leaf carrying the same bytes — no origin tag exists to distinguish them.
        let via_child_root = Subtree::Leaf(child_root.clone());
        let via_raw_payload = Subtree::Leaf(child_root.clone());
        assert_eq!(via_child_root, via_raw_payload);

        // The spine evaluates both identically: same digest, no branching on origin.
        assert_eq!(
            evaluate(&hasher, &via_child_root),
            evaluate(&hasher, &via_raw_payload)
        );
    }
}
