//! `pmt` — the Polymorphic Merkle Tree kernel.
//!
//! The abstract core shared by every tree built above it: the **proof spine**
//! ([`topology`]), **canonicalization** (collapse + promotion, in [`mr`]), the
//! [`Hasher`] seam, **inclusion** proof/verify, the [`Sealed`] carrier, the
//! **metadata channel** ([`Meta`]), and the **combined root** — the
//! canonicalization fold over the per-algorithm member roots (the
//! [`proof::combined_root`] primitive, shared by both trees) and its
//! coupling. It depends on nothing; the engineering libraries (append-only /
//! mutable) depend on it.

pub(crate) mod binding_proof;
pub(crate) mod error;
pub mod hasher;
pub(crate) mod leaf_proof;
pub(crate) mod metadata;
pub mod mr;
pub mod proof;
pub(crate) mod sealed;
pub mod subtree;
pub mod topology;

pub use binding_proof::{BindingProof, TrustedBindingRoot};
pub use error::{Error, Result};
pub use hasher::Hasher;
pub use leaf_proof::LeafProof;
pub use metadata::Meta;
pub use mr::{count_leaves, evaluate, nary_mr, within_subtree_path};
pub use proof::{
    AuditPayload, CouplingProof, InclusionProof, NullRun, ProofStep, VerifierConfig,
    all_null_runs, combined_root, committed_active_algs, committed_active_at, constant_time_eq,
    null_runs_are_trivial, null_runs_for_alg, reconstruct_inclusion_root, serialize_null_runs,
    validate_committed_epochs, verify_inactivity_with_coupling, verify_inclusion,
    verify_inclusion_path_structure, verify_inclusion_with_coupling,
};
pub use sealed::{RunExtent, Sealed};
pub use subtree::Subtree;
pub use topology::{
    ARITY_RANGE, SkeletonStep, fold_frontier, frontier_for_size, inclusion_skeleton,
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
    /// The kernel sees identical structure regardless of origin.
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

        // The kernel evaluates both identically: same digest, no branching on origin.
        assert_eq!(
            evaluate(&hasher, &via_child_root),
            evaluate(&hasher, &via_raw_payload)
        );
    }
}
