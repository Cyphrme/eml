//! `pmt` — the Polymorphic Merkle Tree kernel.
//!
//! The abstract core shared by every tree built above it: the **proof spine**
//! ([`topology`]), **canonicalization** (collapse + promotion, in [`mr`]), the
//! [`Hasher`] seam, **inclusion** proof/verify, **embedding** (an opaque
//! child-tree root as a leaf), the [`Sealed`] carrier, and **epoch
//! construction** — the per-algorithm binding root (the literal
//! `combined_root_*` symbols) and its coupling. It depends on nothing; the
//! engineering libraries (append-only / mutable) depend on it.

pub mod error;
pub mod hasher;
pub mod mr;
pub mod proof;
pub mod sealed;
pub mod subtree;
pub mod topology;

pub use error::{Error, Result};
pub use hasher::Hasher;
pub use mr::{count_leaves, evaluate, nary_mr, within_subtree_path};
pub use proof::{
    AuditPayload, CouplingProof, InclusionProof, ProofStep, VerifierConfig, combined_root_preimage,
    committed_active_algs, committed_active_at, committed_is_live, constant_time_eq,
    reconstruct_inclusion_root, validate_committed_epochs, verify_inactivity_with_coupling,
    verify_inclusion, verify_inclusion_path_structure, verify_inclusion_with_coupling,
};
pub use sealed::Sealed;
pub use subtree::{Subtree, embed, extract};
pub use topology::{SkeletonStep, frontier_for_size, inclusion_skeleton};

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

    /// An embedded child root reads back byte-identically and is opaque: the
    /// embedded leaf is indistinguishable from a raw-payload leaf carrying the
    /// same bytes.
    #[test]
    fn embed_round_trips_and_is_opaque() {
        let hasher = Sha256Hasher;
        let child_root = evaluate(
            &hasher,
            &Subtree::Node(vec![
                Subtree::Leaf(b"a".to_vec()),
                Subtree::Leaf(b"b".to_vec()),
            ]),
        );

        let leaf = embed(child_root.clone());
        assert_eq!(extract(&leaf), Some(child_root.as_slice()));

        // Opaque: a raw-payload leaf with the same bytes is the same value.
        assert_eq!(leaf, Subtree::Leaf(child_root.clone()));
        // An internal node has nothing to extract.
        assert_eq!(extract(&Subtree::Node(vec![leaf])), None);
    }
}
