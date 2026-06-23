//! Inclusion proof structures, verification, and epoch construction.
//!
//! # Security boundary: skeleton-pinned, prefix-chained
//!
//! An inclusion proof path runs leaf → root and splits into two regions:
//!
//! - The **log skeleton** — the trailing steps along the fixed-arity proof spine. Their shape
//!   (count, per-step position and sibling count) is fully determined by `(index, tree_size,
//!   log_arity)` and is pinned exactly against [`crate::topology::inclusion_skeleton`]. Because
//!   there is no per-node domain separation, second-preimage safety rests entirely on this
//!   exactness: the verifier reconstructs the canonical topology and rejects any deviation.
//! - The **subtree prefix** — the leading steps below the leaf's log position, in
//!   application-defined (non-uniform) subtrees. These carry no topological claim and are verified
//!   by hash chaining alone.
//!
//! ## Canonical proof encoding
//!
//! Every accepted step hashes: it must carry at least one sibling. A zero-sibling
//! step would represent a *promoted* (lone-child) node, whose parent equals its
//! child without any hashing — an inert no-op. Such steps are therefore rejected
//! everywhere ([`reconstruct_inclusion_root`]), and honest provers omit them
//! ([`crate::within_subtree_path`]). Omitting a promoted step never changes the
//! computed root, so completeness is preserved; in exchange, a fixed
//! `(leaf_hash, index, tree_size, root)` admits at most one accepting path
//! (modulo hash collisions), which closes prepend/insert malleability. This
//! concerns zero-*sibling* steps only; null-*valued* siblings from a null
//! collapse are unaffected.

use crate::hasher::Hasher;
use crate::mr::nary_mr;
use crate::topology::inclusion_skeleton;

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

/// Verify an inclusion proof.
///
/// Returns `true` if the proof demonstrates that `leaf_hash` is the leaf at
/// `index` in a tree of size `tree_size` and arity `log_arity` whose root is
/// `root`.
///
/// # Trust contract (security-critical)
///
/// `index`, `tree_size`, `log_arity`, and `root` are **trusted parameters**.
/// Soundness comes from the verifier reconstructing the exact tree topology
/// from `(tree_size, log_arity, index)` and rejecting any deviation; the proof
/// supplies only sibling digests. These parameters MUST therefore be obtained
/// from an authenticated source — a signed Tree Head (STH) or trusted
/// checkpoint — and never from the proof itself or any caller-untrusted input.
/// If `tree_size`/`index` are attacker-controlled the guarantee is vacuous: the
/// attacker picks the topology the verifier checks against, and an arbitrary
/// `leaf_hash` can be made to "verify" against a matching forged `root`.
///
/// A `true` result binds `leaf_hash` to log position `index` only. The cell's
/// payload and activity are not asserted here — activity is read from the
/// committed epoch timeline, never inferred from a digest.
#[must_use]
pub fn verify_inclusion(
    hasher: &dyn Hasher,
    leaf_hash: &[u8],
    index: u64,
    tree_size: u64,
    log_arity: u64,
    path: &[ProofStep],
    root: &[u8],
) -> bool {
    reconstruct_inclusion_root(hasher, leaf_hash, index, tree_size, log_arity, path)
        .is_some_and(|computed| constant_time_eq(&computed, root))
}

// ============================================================================
// Committed epoch timeline — epoch construction
// ============================================================================
//
// The binding root is a per-algorithm structural metaroot: an extra layer
// that, like any node, commits what is below it — the member roots. Its
// preimage also covers the per-algorithm epoch timeline `(activation,
// deactivation)` as it stood at that size, because the timeline is part of the
// multi-algorithm structure (it decides which cells are null projections).
// Activity at a position is read from this committed field — never inferred
// from a digest equaling the null constant — which renders the
// `leaf(b"null") == null()` collision inert without forbidding any payload.

/// Canonical preimage of the binding root.
///
/// Layout (all integers `u64` big-endian; fixed-width counts and lengths make
/// the encoding unambiguous to parse and therefore injective):
///
/// ```text
/// n_active ‖ [ id ‖ root_len ‖ root ]*
/// n_algs   ‖ [ id ‖ n_epochs ‖ (start ‖ end)* ]*
/// ```
///
/// `active_roots` lists the raw roots of algorithms active at the tree size;
/// `alg_epochs` lists the committed epoch timeline of every registered
/// algorithm (active and frozen). An epoch open at that size is encoded with
/// `end == u64::MAX`.
#[must_use]
pub fn combined_root_preimage(
    active_roots: &[(u64, Vec<u8>)],
    alg_epochs: &[(u64, Vec<(u64, u64)>)],
) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(&(active_roots.len() as u64).to_be_bytes());
    for (id, r) in active_roots {
        buf.extend_from_slice(&id.to_be_bytes());
        buf.extend_from_slice(&(r.len() as u64).to_be_bytes());
        buf.extend_from_slice(r);
    }
    buf.extend_from_slice(&(alg_epochs.len() as u64).to_be_bytes());
    for (id, epochs) in alg_epochs {
        buf.extend_from_slice(&id.to_be_bytes());
        buf.extend_from_slice(&(epochs.len() as u64).to_be_bytes());
        for &(start, end) in epochs {
            buf.extend_from_slice(&start.to_be_bytes());
            buf.extend_from_slice(&end.to_be_bytes());
        }
    }
    buf
}

/// Validate the structural well-formedness of a committed epoch timeline at
/// `tree_size`: entries strictly sorted by algorithm ID; at least one epoch
/// per algorithm; intervals ordered and non-overlapping (`start <= end`,
/// `start >= prior end`); only the final interval may be open
/// (`end == u64::MAX`); closed ends and open starts do not exceed `tree_size`.
#[must_use]
pub fn validate_committed_epochs(alg_epochs: &[(u64, Vec<(u64, u64)>)], tree_size: u64) -> bool {
    if alg_epochs.windows(2).any(|w| w[0].0 >= w[1].0) {
        return false;
    }
    for (_, epochs) in alg_epochs {
        if epochs.is_empty() {
            return false;
        }
        let mut last_end = 0u64;
        for (i, &(start, end)) in epochs.iter().enumerate() {
            if start > end || start < last_end {
                return false;
            }
            if end == u64::MAX {
                if i != epochs.len() - 1 || start > tree_size {
                    return false;
                }
            } else if end > tree_size {
                return false;
            }
            last_end = end;
        }
    }
    true
}

/// Read the authenticated activity of `alg_id` at position `index` from a
/// committed epoch timeline. Returns `None` if the algorithm has no committed
/// timeline.
#[must_use]
pub fn committed_active_at(
    alg_epochs: &[(u64, Vec<(u64, u64)>)],
    alg_id: u64,
    index: u64,
) -> Option<bool> {
    let idx = alg_epochs
        .binary_search_by_key(&alg_id, |&(id, _)| id)
        .ok()?;
    Some(
        alg_epochs[idx]
            .1
            .iter()
            .any(|&(start, end)| start <= index && index < end),
    )
}

/// Whether `alg_id` is live (final epoch still open) at the snapshot this
/// timeline was committed at. Returns `None` if the algorithm has no
/// committed timeline.
///
/// This answers the frontier-freshness query "is this key live right now?",
/// which is not derivable from the tree alone: a deactivation at the idle log
/// tip leaves no later positions to witness it.
#[must_use]
pub fn committed_is_live(alg_epochs: &[(u64, Vec<(u64, u64)>)], alg_id: u64) -> Option<bool> {
    let idx = alg_epochs
        .binary_search_by_key(&alg_id, |&(id, _)| id)
        .ok()?;
    Some(
        alg_epochs[idx]
            .1
            .last()
            .is_some_and(|&(_, end)| end == u64::MAX),
    )
}

/// Derive the active algorithm set at `tree_size` from a committed timeline:
/// the algorithms whose epochs cover the final position `tree_size - 1`.
/// Returned sorted by algorithm ID (inherited from the timeline ordering).
#[must_use]
pub fn committed_active_algs(alg_epochs: &[(u64, Vec<(u64, u64)>)], tree_size: u64) -> Vec<u64> {
    if tree_size == 0 {
        return Vec::new();
    }
    let last = tree_size - 1;
    alg_epochs
        .iter()
        .filter(|(_, epochs)| {
            epochs
                .iter()
                .any(|&(start, end)| start <= last && last < end)
        })
        .map(|&(id, _)| id)
        .collect()
}

/// Configuration options for proof verification (local node policy).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VerifierConfig {
    /// Maximum number of active algorithms allowed (DoS mitigation).
    pub max_active_algorithms: usize,
    /// Maximum number of algorithms (active and frozen) in a committed epoch
    /// timeline (DoS mitigation).
    pub max_algorithms: usize,
    /// Maximum number of epoch intervals per algorithm (DoS mitigation).
    pub max_epochs_per_algorithm: usize,
}

impl Default for VerifierConfig {
    fn default() -> Self {
        Self {
            max_active_algorithms: 8,
            max_algorithms: 64,
            max_epochs_per_algorithm: 1024,
        }
    }
}

/// A coupling proof that opens a binding root to its children: the raw
/// algorithm roots together with the committed epoch timeline. This is the
/// metadata-opening segment of inclusion/inactivity proofs: once authenticated
/// against the binding root, `alg_epochs` is the trusted source for
/// `active(X, p)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CouplingProof {
    /// The active roots at this tree size: (alg_id, raw_root_hash)
    pub active_roots: Vec<(u64, Vec<u8>)>,
    /// The committed epoch timeline at this tree size: `(alg_id, epochs)` for
    /// every registered algorithm (active and frozen), sorted by algorithm
    /// ID. Authenticated against the binding root together with the roots.
    pub alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
}

impl CouplingProof {
    /// Authenticate the proof against a binding root at `tree_size`.
    ///
    /// Validates structure (canonical ordering, bounds, well-formed epochs,
    /// active set consistent with the timeline) and reconstructs the
    /// binding-root preimage via [`combined_root_preimage`]. On success both
    /// `active_roots` and `alg_epochs` are authenticated by the root.
    #[must_use]
    pub fn authenticate(
        &self,
        hasher: &dyn Hasher,
        tree_size: u64,
        combined_root: &[u8],
        expected_active_algs: &[u64],
        config: VerifierConfig,
    ) -> bool {
        // Nothing is committed at size zero.
        if tree_size == 0 {
            return false;
        }

        // DoS Mitigation: assert counts do not exceed configuration limits
        // before allocating.
        if self.active_roots.len() > config.max_active_algorithms {
            return false;
        }
        if self.alg_epochs.len() > config.max_algorithms {
            return false;
        }
        if self
            .alg_epochs
            .iter()
            .any(|(_, e)| e.len() > config.max_epochs_per_algorithm)
        {
            return false;
        }

        // Validate active roots match expected active algorithms exactly to prevent
        // type-confusion/bypass
        if self.active_roots.len() != expected_active_algs.len() {
            return false;
        }
        for ((id, _), &expected_id) in self.active_roots.iter().zip(expected_active_algs.iter()) {
            if *id != expected_id {
                return false;
            }
        }

        // DoS Mitigation: assert individual companion root sizes are within bounds
        for (_, r) in &self.active_roots {
            if r.len() > 64 {
                return false;
            }
        }

        // Ensure the active roots list is canonically sorted by algorithm ID (prover requirement)
        // to prevent duplicate representation vectors or sorting malleability.
        if self.active_roots.windows(2).any(|w| w[0].0 >= w[1].0) {
            return false;
        }

        // The committed timeline must be well-formed and must imply exactly
        // the claimed active set: an algorithm cannot present a root without
        // a covering epoch, nor claim an epoch covering the tip without a
        // root.
        if !validate_committed_epochs(&self.alg_epochs, tree_size) {
            return false;
        }
        let derived = committed_active_algs(&self.alg_epochs, tree_size);
        if derived.len() != self.active_roots.len()
            || derived
                .iter()
                .zip(self.active_roots.iter())
                .any(|(&d, &(id, _))| d != id)
        {
            return false;
        }

        // Reconstruct the binding root mirroring the genesis-promotion rule in
        // the constructor: a registry-singleton with the forced default
        // timeline [(0, MAX)] means the binding root IS the raw root of that
        // algorithm (promoted form); otherwise hash the canonical preimage.
        let is_promoted =
            self.alg_epochs.len() == 1 && self.alg_epochs[0].1 == vec![(0u64, u64::MAX)];
        if is_promoted {
            constant_time_eq(&self.active_roots[0].1, combined_root)
        } else {
            let computed = hasher.hash(&combined_root_preimage(
                &self.active_roots,
                &self.alg_epochs,
            ));
            constant_time_eq(&computed, combined_root)
        }
    }

    /// Verify the coupling proof against a binding root for a given target algorithm.
    /// Returns the verified raw root hash for the target algorithm if successful.
    #[must_use]
    pub fn verify(
        &self,
        hasher: &dyn Hasher,
        target_alg_id: u64,
        tree_size: u64,
        combined_root: &[u8],
        expected_active_algs: &[u64],
        config: VerifierConfig,
    ) -> Option<Vec<u8>> {
        if !self.authenticate(
            hasher,
            tree_size,
            combined_root,
            expected_active_algs,
            config,
        ) {
            return None;
        }

        // Extract the target algorithm's root
        self.active_roots
            .iter()
            .find(|&&(id, _)| id == target_alg_id)
            .map(|(_, r)| r.clone())
    }
}

/// Validate that the trailing steps of an inclusion proof path match the
/// log-spine skeleton pinned by `(index, tree_size, k)`.
///
/// The skeleton — its length and, per step, the path node's position and sibling
/// count — is derived once by [`inclusion_skeleton`], the single authority on log
/// topology shared with proof generation. The trailing `skeleton.len()` steps are
/// checked field-by-field against it; the leading `path.len() - skeleton.len()`
/// steps are the subtree portion and carry no topological claim here (they are
/// verified by hash chaining in [`reconstruct_inclusion_root`]).
#[must_use]
pub fn verify_inclusion_path_structure(
    k: usize,
    index: u64,
    tree_size: u64,
    path: &[ProofStep],
) -> bool {
    let skeleton = match inclusion_skeleton(k as u64, tree_size, index) {
        Some(s) => s,
        None => return false,
    };
    if path.len() < skeleton.len() {
        return false;
    }
    let d = path.len() - skeleton.len();
    path[d..]
        .iter()
        .zip(skeleton.iter())
        .all(|(step, shape)| step.shape() == *shape)
}

/// Reconstruct the raw root from an inclusion proof path.
///
/// Building block for [`verify_inclusion`]; it computes a root but does not
/// compare it to a trusted one. Callers must hold to the same trust contract:
/// `index`, `tree_size`, and `log_arity` must be authenticated (see
/// [`verify_inclusion`]), and the returned root is only meaningful when checked
/// against an authenticated root.
#[must_use]
pub fn reconstruct_inclusion_root(
    hasher: &dyn Hasher,
    leaf_hash: &[u8],
    index: u64,
    tree_size: u64,
    log_arity: u64,
    path: &[ProofStep],
) -> Option<Vec<u8>> {
    let digest_len = hasher.empty().len();
    if digest_len == 0 || digest_len > 64 {
        return None;
    }
    if leaf_hash.len() != digest_len {
        return None;
    }
    if !(2..=256).contains(&log_arity) {
        return None;
    }
    if tree_size == 0 {
        return None;
    }
    if index >= tree_size {
        return None;
    }
    if path.len() > 256 {
        return None;
    }

    if !verify_inclusion_path_structure(log_arity as usize, index, tree_size, path) {
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
            // (leaf_hash, index, tree_size, root). See the module docs.
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

/// Helper wrapper demonstrating inclusion verification with decoupled coupling proofs.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn verify_inclusion_with_coupling(
    hasher: &dyn Hasher,
    alg_id: u64,
    leaf_hash: &[u8],
    index: u64,
    tree_size: u64,
    log_arity: u64,
    path: &[ProofStep],
    coupling: &CouplingProof,
    combined_root: &[u8],
    expected_active_algs: &[u64],
    config: VerifierConfig,
) -> bool {
    let raw_root = match coupling.verify(
        hasher,
        alg_id,
        tree_size,
        combined_root,
        expected_active_algs,
        config,
    ) {
        Some(r) => r,
        None => return false,
    };

    // One-directional inactive⇒N₀ check: if the committed timeline marks
    // this position INACTIVE for alg_id, the leaf hash must equal the null
    // constant.  Active positions are unconstrained — a legitimate payload
    // `b"null"` hashes to null() but is never forbidden.  `None` (algorithm
    // not in the timeline at all) is rejected as an ill-formed proof.
    match committed_active_at(&coupling.alg_epochs, alg_id, index) {
        Some(false) => {
            if !constant_time_eq(leaf_hash, &hasher.null()) {
                return false;
            }
        },
        Some(true) => {},
        None => return false,
    }

    verify_inclusion(
        hasher, leaf_hash, index, tree_size, log_arity, path, &raw_root,
    )
}

/// Verify an inactivity claim for a leaf at `index` using a coupling proof.
///
/// Succeeds iff:
/// - `index < tree_size`
/// - The coupling proof authenticates against `combined_root`.
/// - The committed timeline marks `alg_id` **inactive** at `index`.
/// - If `alg_id` has a committed root (it appears in `coupling.active_roots`), an inclusion proof
///   for the null constant at `index` verifies against that root.  The caller must provide the
///   matching Merkle path.
/// - If `alg_id` is frozen at `tree_size` (no committed root), `path` must be empty — the committed
///   timeline alone is sufficient evidence.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn verify_inactivity_with_coupling(
    hasher: &dyn Hasher,
    alg_id: u64,
    index: u64,
    tree_size: u64,
    log_arity: u64,
    path: &[ProofStep],
    coupling: &CouplingProof,
    combined_root: &[u8],
    expected_active_algs: &[u64],
    config: VerifierConfig,
) -> bool {
    if index >= tree_size {
        return false;
    }

    if !coupling.authenticate(
        hasher,
        tree_size,
        combined_root,
        expected_active_algs,
        config,
    ) {
        return false;
    }

    // Position must be committed-inactive for this algorithm.
    match committed_active_at(&coupling.alg_epochs, alg_id, index) {
        Some(false) => {},
        _ => return false,
    }

    // If alg_id has an active committed root, open it with a null-leaf
    // inclusion proof.  If it is frozen (not in active_roots), the timeline
    // commitment alone is the evidence and the path must be empty.
    if let Some((_, raw_root)) = coupling.active_roots.iter().find(|&&(id, _)| id == alg_id) {
        verify_inclusion(
            hasher,
            &hasher.null(),
            index,
            tree_size,
            log_arity,
            path,
            raw_root,
        )
    } else {
        path.is_empty()
    }
}

/// The raw payload of an audit verification checkpoint.
///
/// This is the agnostic attestation payload: an out-of-band signer may sign
/// this struct to produce a checkpoint attestation, but the kernel never
/// interprets, signs, or reaches consensus over it — the type names no signing
/// scheme or envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuditPayload {
    /// Identifier of the log being audited.
    pub log_id: [u8; 32],
    /// The tree size that was verified.
    pub tree_size: u64,
    /// The list of active algorithm IDs at this checkpoint size.
    pub active_algs: Vec<u64>,
    /// The binding roots of the log at `tree_size` for each active algorithm.
    pub combined_roots: Vec<(u64, Vec<u8>)>,
    /// Committed epoch timeline at `tree_size`: `(alg_id, epochs)` for every
    /// registered algorithm (active and frozen), sorted by algorithm ID.
    /// Same value as `committed_epochs_at(tree_size)`.  Binding the timeline
    /// into the payload lets the signing attestation cover activation/
    /// deactivation boundaries, making activity claims non-equivocable.
    pub alg_epochs: Vec<(u64, Vec<(u64, u64)>)>,
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAX: u64 = u64::MAX;

    #[test]
    fn test_combined_root_preimage_injective_sections() {
        // Moving an interval between algorithms or shifting a boundary must
        // change the encoding.
        let roots = vec![(0u64, vec![0xAA; 32])];
        let a = combined_root_preimage(&roots, &[(0, vec![(0, MAX)])]);
        let b = combined_root_preimage(&roots, &[(0, vec![(1, MAX)])]);
        let c = combined_root_preimage(&roots, &[(0, vec![(0, 5)])]);
        let d = combined_root_preimage(&roots, &[(0, vec![(0, 5), (7, MAX)])]);
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(c, d);
        // Empty epoch section differs from empty active section swap.
        let e = combined_root_preimage(&[], &[(0, vec![(0, MAX)])]);
        let f = combined_root_preimage(&roots, &[]);
        assert_ne!(e, f);
    }

    #[test]
    fn test_validate_committed_epochs() {
        // Well-formed: closed, open, gap + resume.
        assert!(validate_committed_epochs(&[(0, vec![(0, MAX)])], 10));
        assert!(validate_committed_epochs(&[(0, vec![(0, 5)])], 10));
        assert!(validate_committed_epochs(
            &[(0, vec![(0, 3), (5, MAX)]), (1, vec![(2, 2)])],
            10
        ));
        // Resume at the deactivation boundary is legal.
        assert!(validate_committed_epochs(
            &[(0, vec![(0, 5), (5, MAX)])],
            10
        ));

        // Unsorted / duplicate algorithm IDs.
        assert!(!validate_committed_epochs(
            &[(1, vec![(0, MAX)]), (0, vec![(0, MAX)])],
            10
        ));
        assert!(!validate_committed_epochs(
            &[(0, vec![(0, MAX)]), (0, vec![(0, MAX)])],
            10
        ));
        // Empty timeline.
        assert!(!validate_committed_epochs(&[(0, vec![])], 10));
        // Overlap / disorder.
        assert!(!validate_committed_epochs(
            &[(0, vec![(0, 5), (4, MAX)])],
            10
        ));
        assert!(!validate_committed_epochs(&[(0, vec![(5, 3)])], 10));
        // Open epoch not last.
        assert!(!validate_committed_epochs(
            &[(0, vec![(0, MAX), (1, 2)])],
            10
        ));
        // Bounds beyond the snapshot size.
        assert!(!validate_committed_epochs(&[(0, vec![(0, 11)])], 10));
        assert!(!validate_committed_epochs(&[(0, vec![(11, MAX)])], 10));
        // Closed exactly at the snapshot size is legal (frontier deactivation).
        assert!(validate_committed_epochs(&[(0, vec![(0, 10)])], 10));
    }

    #[test]
    fn test_committed_activity_reads() {
        let timeline = vec![(0u64, vec![(0u64, 3u64), (5, MAX)]), (1, vec![(0, 10)])];
        assert_eq!(committed_active_at(&timeline, 0, 2), Some(true));
        assert_eq!(committed_active_at(&timeline, 0, 3), Some(false));
        assert_eq!(committed_active_at(&timeline, 0, 4), Some(false));
        assert_eq!(committed_active_at(&timeline, 0, 5), Some(true));
        assert_eq!(committed_active_at(&timeline, 1, 9), Some(true));
        assert_eq!(committed_active_at(&timeline, 2, 0), None);

        assert_eq!(committed_is_live(&timeline, 0), Some(true));
        assert_eq!(committed_is_live(&timeline, 1), Some(false));
        assert_eq!(committed_is_live(&timeline, 2), None);

        // Alg 1's epoch closes exactly at 10, so it still covers position 9.
        assert_eq!(committed_active_algs(&timeline, 10), vec![0, 1]);
        // Position 4 falls in alg 0's gap [3, 5).
        assert_eq!(committed_active_algs(&timeline, 5), vec![1]);
        assert_eq!(committed_active_algs(&timeline, 2), vec![0, 1]);
        assert!(committed_active_algs(&timeline, 0).is_empty());
    }
}
