//! Inclusion proof structures and the **abstract** verifier.
//!
//! # Security boundary: skeleton-pinned, prefix-chained
//!
//! An inclusion proof path runs leaf → root and splits into two regions:
//!
//! - The **structural skeleton** — the trailing steps along the structure's commitment topology.
//!   Their shape (count, per-step position and sibling count) is a [`SkeletonStep`] sequence the
//!   *consumer* computes from its own trusted `(index, tree_size, arity)` and passes in; the
//!   verifier pins the proof's trailing steps against it exactly. Because there is no per-node
//!   domain separation, second-preimage safety rests entirely on this exactness: the verifier
//!   rejects any deviation from the supplied skeleton.
//! - The **subtree prefix** — the leading steps below the leaf's structural position, in
//!   application-defined (non-uniform) subtrees. These carry no topological claim and are verified
//!   by hash chaining alone.
//!
//! The verifier is **topology-agnostic**: it knows the skeleton *mechanism* (pin
//! the trailing steps, hash-chain the prefix) but not the concrete topology. The
//! append-only log supplies a mountain-range skeleton, the mutable tree a
//! rebalanced one; one verifier serves both because the skeleton is the seam.
//! This mirrors the Lean corpus, whose `inclusion_soundness` is stated over an
//! abstract `SkeletonValid` predicate rather than a baked-in topology.
//!
//! ## Canonical proof encoding
//!
//! Every accepted step hashes: it must carry at least one sibling. A zero-sibling
//! step would represent a *promoted* (lone-child) node, whose parent equals its
//! child without any hashing — an inert no-op. Such steps are therefore rejected
//! everywhere ([`reconstruct_inclusion_root`]), and honest provers omit them
//! ([`crate::within_subtree_path`]). Omitting a promoted step never changes the
//! computed root, so completeness is preserved; in exchange, a fixed
//! `(leaf_hash, skeleton, root)` admits at most one accepting path
//! (modulo hash collisions), which closes prepend/insert malleability. This
//! concerns zero-*sibling* steps only; null-*valued* siblings from a null
//! collapse are unaffected.

use crate::hasher::Hasher;
use crate::mr::nary_mr;
use crate::topology::SkeletonStep;

/// A single level in a Merkle proof path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    /// Sibling digests at this level (excluding the path node).
    /// Empty for promoted (lone-child) nodes.
    pub siblings: Vec<Vec<u8>>,
    /// Position of the path node among all children (0-indexed).
    pub position: usize,
}

impl ProofStep {
    /// Project this step's structural shape — position and sibling count —
    /// as a [`crate::topology::SkeletonStep`]. Used by
    /// [`verify_inclusion_path_structure`] to compare against the canonical
    /// skeleton without open-coding the field correspondence.
    #[must_use]
    pub fn shape(&self) -> crate::topology::SkeletonStep {
        crate::topology::SkeletonStep {
            position: self.position,
            sibling_count: self.siblings.len(),
        }
    }
}

/// Inclusion proof: path from a leaf to the root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InclusionProof {
    /// Path steps from leaf to root.
    pub path: Vec<ProofStep>,
}

/// Timing-safe comparison of two byte slices.
#[inline]
pub fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut result = 0;
    for (&x, &y) in a.iter().zip(b.iter()) {
        result |= std::hint::black_box(x) ^ std::hint::black_box(y);
    }
    std::hint::black_box(result) == 0
}

/// Verify an inclusion proof against a consumer-supplied skeleton.
///
/// Returns `true` if `path` demonstrates that `leaf_hash` reaches `root` along a
/// path whose trailing steps match `skeleton` exactly.
///
/// # Trust contract (security-critical)
///
/// `skeleton` and `root` are **trusted parameters**. The skeleton is the
/// structure's canonical topology, computed by the consumer from its own trusted
/// `(index, tree_size, arity)` (an append-only log's mountain skeleton, a mutable
/// tree's rebalanced skeleton). Soundness comes from the verifier pinning the
/// proof's trailing steps against this exact skeleton and rejecting any
/// deviation; the proof itself supplies only sibling digests. The skeleton and
/// root MUST therefore be obtained from an authenticated source — derived from a
/// signed Tree Head (STH) or trusted checkpoint — never from the proof or any
/// caller-untrusted input. If the position/size the skeleton encodes are
/// attacker-controlled the guarantee is vacuous: the attacker picks the topology
/// the verifier checks against, and an arbitrary `leaf_hash` can be made to
/// "verify" against a matching forged `root`.
///
/// A `true` result binds `leaf_hash` to the position the skeleton pins only. The
/// cell's payload and activity are not asserted here — activity is read from the
/// committed epoch timeline (an `epoch` concept), never inferred from a digest.
#[must_use]
pub fn verify_inclusion(
    hasher: &dyn Hasher,
    leaf_hash: &[u8],
    skeleton: &[SkeletonStep],
    path: &[ProofStep],
    root: &[u8],
) -> bool {
    reconstruct_inclusion_root(hasher, leaf_hash, skeleton, path)
        .is_some_and(|computed| constant_time_eq(&computed, root))
}

/// Validate that the trailing steps of an inclusion proof path match the
/// consumer-supplied `skeleton`.
///
/// The skeleton — its length and, per step, the path node's position and sibling
/// count — is the structure's canonical topology, computed once by the consumer
/// (the single authority on its own topology, shared with proof generation). The
/// trailing `skeleton.len()` steps are checked field-by-field against it; the
/// leading `path.len() - skeleton.len()` steps are the subtree portion and carry
/// no topological claim here (they are verified by hash chaining in
/// [`reconstruct_inclusion_root`]).
#[must_use]
pub fn verify_inclusion_path_structure(skeleton: &[SkeletonStep], path: &[ProofStep]) -> bool {
    if path.len() < skeleton.len() {
        return false;
    }
    let d = path.len() - skeleton.len();
    path[d..]
        .iter()
        .zip(skeleton.iter())
        .all(|(step, shape)| step.shape() == *shape)
}

/// Reconstruct the raw root from an inclusion proof path and its trusted
/// skeleton.
///
/// Building block for [`verify_inclusion`]; it computes a root but does not
/// compare it to a trusted one. Callers must hold to the same trust contract:
/// `skeleton` must be authenticated (see [`verify_inclusion`]), and the returned
/// root is only meaningful when checked against an authenticated root. A
/// well-formed skeleton implies the position/size were valid — the consumer that
/// computed it rejects an out-of-range position by producing no skeleton — so the
/// core needs no separate `(index, tree_size, arity)` bounds, only the
/// digest-width and DoS bounds below.
#[must_use]
pub fn reconstruct_inclusion_root(
    hasher: &dyn Hasher,
    leaf_hash: &[u8],
    skeleton: &[SkeletonStep],
    path: &[ProofStep],
) -> Option<Vec<u8>> {
    let digest_len = hasher.empty().len();
    if digest_len == 0 || digest_len > 64 {
        return None;
    }
    if leaf_hash.len() != digest_len {
        return None;
    }
    if path.len() > 256 {
        return None;
    }

    if !verify_inclusion_path_structure(skeleton, path) {
        return None;
    }

    let mut current = leaf_hash.to_vec();

    for step in path {
        if step.siblings.len() > 256 {
            return None;
        }
        for sib in &step.siblings {
            if sib.len() != digest_len {
                return None;
            }
        }
        if step.siblings.is_empty() {
            // Canonical proof encoding: a zero-sibling step would be a promoted
            // (lone-child) node, whose parent equals the child without hashing.
            // Such steps are inert no-ops, so honest provers omit them; rejecting
            // them here makes the accepting path unique for a fixed
            // (leaf_hash, skeleton, root). See the module docs.
            return None;
        }
        if step.position > step.siblings.len() {
            return None;
        }

        // Reconstruct the parent: insert current at position among siblings
        let mut children = Vec::with_capacity(step.siblings.len() + 1);
        for (i, sib) in step.siblings.iter().enumerate() {
            if i == step.position {
                children.push(current.as_slice());
            }
            children.push(sib.as_slice());
        }
        if step.position == step.siblings.len() {
            children.push(current.as_slice());
        }

        current = nary_mr(hasher, &children);
    }

    Some(current)
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;

    #[derive(Debug)]
    struct H;
    impl Hasher for H {
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
            Box::new(H)
        }
    }

    /// A zero-sibling (promoted) step is rejected: the accepting path is unique.
    #[test]
    fn zero_sibling_step_is_rejected() {
        let h = H;
        let leaf = h.leaf(b"x");
        let path = vec![ProofStep {
            siblings: vec![],
            position: 0,
        }];
        // An empty skeleton treats the lone step as a subtree-prefix step; the
        // hash-chaining loop still rejects it because it carries no sibling. A
        // promoted step never reconstructs a root.
        assert_eq!(reconstruct_inclusion_root(&h, &leaf, &[], &path), None);
    }

    /// `constant_time_eq` agrees with `==` on equal and unequal byte slices.
    #[test]
    fn constant_time_eq_matches_equality() {
        assert!(constant_time_eq(b"abc", b"abc"));
        assert!(!constant_time_eq(b"abc", b"abd"));
        assert!(!constant_time_eq(b"abc", b"ab"));
        assert!(constant_time_eq(b"", b""));
    }
}
