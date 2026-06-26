//! The polydigest combinator's root construction and coupling verification.
//!
//! The structural spine ([`spine`]) folds a single tree to a member root. The
//! polydigest combinator lifts that across N algorithms over one shared data
//! substrate: it adds the **activation timeline**, the **null-run-extents** (the
//! one logical count), and the **binding root** — the atomic multi-tree
//! commitment. None of this lives in the structural core.
//!
//! # Combined (binding) root — the canonicalization fold over the member-root children
//!
//! The combined root is the structural metaroot of a multi-algorithm tree: the
//! canonicalization fold ([`spine::nary_mr`] — collapse + promotion) applied one
//! level up, over the per-algorithm **member roots** as children. It is the live
//! primary root of both the append-only log and the mutable tree, and the head
//! the per-algorithm member roots authenticate against.
//!
//! Two facts make this a fold, not a bespoke hash:
//!
//! - **Genesis-promotion is native.** A registry of one algorithm folds `nary_mr(H, [MR_0])`, whose
//!   `len == 1` arm promotes to `MR_0` — the combined root *is* the member root because there is
//!   one child, not because of a special case. There is no promotion predicate.
//! - **Coverage is a sibling, present only when informative.** The committed epoch timeline decides
//!   which cells are null projections, so a multi-algorithm structure must commit it. It enters the
//!   fold as one extra child `C = H_i(serialize(timeline))`, appended **iff the timeline is
//!   non-trivial** (some algorithm has anything other than the open-from-genesis epoch `[(0,
//!   u64::MAX)]`). A trivial timeline carries no information beyond the member roots, so its child
//!   is omitted; absence of the child *is* the trivial encoding (the same way same-value collapse
//!   treats the null case). The timeline is independently bound by [`AuditPayload`], so omitting
//!   the in-root copy on the trivial case loses no security.
//!
//! Activity at a position is read from the committed timeline — never inferred
//! from a digest equaling the null constant — which renders the
//! `leaf(b"null") == null()` collision inert without forbidding any payload.

use spine::{ARITY_RANGE, Hasher, ProofStep, constant_time_eq, nary_mr, verify_inclusion};

/// One null collapse run of a single algorithm: the algorithm projects to the
/// null constant across the aligned k-ary block `[left, left + k^height)`.
///
/// This is the **null subset** of the general collapse run-extents — the only
/// per-algorithm-divergent collapse, hence the minimal committed activation
/// information. Non-null equal-value runs are mirrored across every algorithm's
/// tree and recovered from the shared data, so they are never tracked here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NullRun {
    /// First leaf index of the null block.
    pub left: u64,
    /// Height of the aligned k-ary null block; it spans `arity^height` leaves.
    /// `height == 0` is a single inactive leaf.
    pub height: u32,
}

/// Decompose algorithm `eps`'s **inactive** positions in `[0, tree_size)` into
/// the canonical null collapse runs: the maximal aligned `k`-ary blocks the
/// tree folds to null, greatest-block-first within each contiguous inactive
/// span (the same greedy decomposition [`spine::frontier_for_size`] applies to
/// the whole tree, here applied to each inactive gap).
///
/// This is the committed activation in geometric form. It is a *canonical
/// function of the active intervals* `eps` and `(tree_size, arity)`: the union
/// of the returned block spans is exactly the inactive position set, so the
/// active set — and therefore `eps` in canonical form — is recoverable as the
/// complement. Committing these runs commits the identical activity the epoch
/// intervals carry.
///
/// The inactive set is computed **interval-wise** — the complement of the active
/// epochs, derived by merging them and taking the gaps within `[0, tree_size)` —
/// not by scanning each position. Cost is `O(#epochs · log #epochs)` plus the
/// per-gap block decomposition, so the fully-active canonical form `[(0, MAX)]`
/// early-outs to an empty vector and the binding root folds in `O(log n)`.
#[must_use]
pub fn null_runs_for_alg(eps: &[(u64, u64)], tree_size: u64, arity: u64) -> Vec<NullRun> {
    // Normalize the active epochs into a sorted, disjoint cover of [0, tree_size):
    // clip each interval to the tree, drop empties, then merge overlaps. The gaps
    // between the merged actives are the maximal contiguous inactive spans —
    // identical to those a position-by-position scan would find, but without
    // touching every position. `eps` may be unsorted or overlapping (callers and
    // adversarial proofs present arbitrary slices), which the merge tolerates.
    let mut active: Vec<(u64, u64)> = eps
        .iter()
        .filter_map(|&(s, e)| {
            let s = s.min(tree_size);
            let e = e.min(tree_size);
            (s < e).then_some((s, e))
        })
        .collect();
    active.sort_unstable();
    let mut merged: Vec<(u64, u64)> = Vec::with_capacity(active.len());
    for (s, e) in active {
        match merged.last_mut() {
            Some(last) if s <= last.1 => last.1 = last.1.max(e),
            _ => merged.push((s, e)),
        }
    }

    // Walk the inactive gaps (the complement of `merged` within [0, tree_size))
    // and decompose each into the canonical null runs.
    let mut runs = Vec::new();
    let mut cursor = 0u64;
    for (s, e) in merged {
        decompose_inactive_gap(cursor, s, arity, &mut runs);
        cursor = e;
    }
    decompose_inactive_gap(cursor, tree_size, arity, &mut runs);
    runs
}

/// Greedy aligned-block decomposition of the inactive gap `[left_bound, right)`:
/// at each position emit the largest aligned k-ary block that fits and stays
/// inside the gap, then advance. This is the same greedy decomposition
/// [`spine::frontier_for_size`] applies to a whole tree, here applied to one
/// gap; it reproduces the original per-position scan's inner loop exactly, so
/// the emitted runs are byte-identical.
fn decompose_inactive_gap(left_bound: u64, right: u64, arity: u64, runs: &mut Vec<NullRun>) {
    let mut left = left_bound;
    while left < right {
        let mut height = 0u32;
        // Grow the block while it stays aligned at `left` and within `[left_bound, right)`.
        loop {
            let next_h = height + 1;
            let span = match arity.checked_pow(next_h) {
                Some(s) => s,
                None => break,
            };
            // Aligned at `left` (left % span == 0) and fits within the gap.
            if left % span == 0 && left + span <= right {
                height = next_h;
            } else {
                break;
            }
        }
        runs.push(NullRun { left, height });
        left += arity.pow(height);
    }
}

/// All algorithms' null collapse runs at `(tree_size, arity)`, derived from the
/// committed epoch intervals: `(alg_id, runs)` for every registered algorithm,
/// sorted by algorithm ID, omitting algorithms with no null run (fully active
/// over `[0, tree_size)`). This is the activation committed in **every** binding
/// root; the redundancy physically binds the trees.
#[must_use]
pub fn all_null_runs(
    alg_epochs: &[(u64, Vec<(u64, u64)>)],
    tree_size: u64,
    arity: u64,
) -> Vec<(u64, Vec<NullRun>)> {
    let mut out: Vec<(u64, Vec<NullRun>)> = alg_epochs
        .iter()
        .filter_map(|(id, eps)| {
            let runs = null_runs_for_alg(eps, tree_size, arity);
            if runs.is_empty() {
                None
            } else {
                Some((*id, runs))
            }
        })
        .collect();
    out.sort_unstable_by_key(|&(id, _)| id);
    out
}

/// Whether the committed activation is **trivial**: no algorithm has any null
/// run over `[0, tree_size)` (every registered algorithm is fully active). A
/// trivial activation carries no information beyond the member roots, so the
/// binding-root fold omits its coverage child — absence of the child *is* the
/// trivial encoding.
#[must_use]
pub fn null_runs_are_trivial(
    alg_epochs: &[(u64, Vec<(u64, u64)>)],
    tree_size: u64,
    arity: u64,
) -> bool {
    all_null_runs(alg_epochs, tree_size, arity).is_empty()
}

/// Canonical serialization of all algorithms' null runs — the preimage of the
/// binding root's coverage child; the committed activation form.
///
/// Layout (all integers big-endian; fixed-width counts make it unambiguous to
/// parse, hence injective):
///
/// ```text
/// arity ‖ tree_size ‖ n_algs ‖ [ id ‖ n_runs ‖ (left ‖ height)* ]*
/// ```
///
/// `arity` and `tree_size` are bound so the geometric runs cannot be reinterpreted
/// under a different spine; `(left : u64, height : u32)` per run.
#[must_use]
pub fn serialize_null_runs(
    alg_epochs: &[(u64, Vec<(u64, u64)>)],
    tree_size: u64,
    arity: u64,
) -> Vec<u8> {
    let all = all_null_runs(alg_epochs, tree_size, arity);
    let mut buf = Vec::new();
    buf.extend_from_slice(&arity.to_be_bytes());
    buf.extend_from_slice(&tree_size.to_be_bytes());
    buf.extend_from_slice(&(all.len() as u64).to_be_bytes());
    for (id, runs) in &all {
        buf.extend_from_slice(&id.to_be_bytes());
        buf.extend_from_slice(&(runs.len() as u64).to_be_bytes());
        for r in runs {
            buf.extend_from_slice(&r.left.to_be_bytes());
            buf.extend_from_slice(&r.height.to_be_bytes());
        }
    }
    buf
}

/// The combined root: the canonicalization fold ([`spine::nary_mr`]) over the
/// per-algorithm member roots as children, under one algorithm's own hash `H`.
///
/// The children are the member roots in `member_roots` order (the caller pins
/// canonical sort by algorithm ID), followed by a single **coverage child**
/// `H(serialize_null_runs(alg_epochs, tree_size, arity))` committing **all
/// algorithms' null-run-extents**, present **iff** the activation is non-trivial
/// ([`null_runs_are_trivial`] — some algorithm has a null run). They form the
/// children of one [`spine::nary_mr`] node, so collapse + promotion apply
/// exactly as they do everywhere else:
///
/// - one child (single algorithm, fully active) ⇒ the combined root **is** the member root (genesis
///   promotion, native — no predicate);
/// - many children ⇒ `nary_mr(H, children)`.
///
/// The coverage child is the **activation commitment**: the null-valued
/// run-extents are the only per-tree-divergent collapse, so they are the minimal
/// information needed to reconstruct the multi-tree structure, and **every**
/// binding root commits **every** algorithm's null runs — that redundancy is
/// what physically binds the trees. The activity an inactivity/coupling proof
/// reads is grounded in these committed runs (the runs cover exactly the
/// inactive positions, so the active set is their complement).
///
/// `member_roots` carries the *raw* per-algorithm roots as opaque digests; `H`
/// is only ever applied to those digests (and the null-run serialization), never
/// to another algorithm's security material — so each algorithm's combined root
/// rests solely on its own hash (no security mixing).
#[must_use]
pub fn combined_root(
    hasher: &dyn Hasher,
    member_roots: &[(u64, Vec<u8>)],
    alg_epochs: &[(u64, Vec<(u64, u64)>)],
    tree_size: u64,
    arity: u64,
) -> Vec<u8> {
    let mut children: Vec<Vec<u8>> = member_roots.iter().map(|(_, r)| r.clone()).collect();
    if !null_runs_are_trivial(alg_epochs, tree_size, arity) {
        children.push(hasher.hash(&serialize_null_runs(alg_epochs, tree_size, arity)));
    }
    let refs: Vec<&[u8]> = children.iter().map(|c| c.as_slice()).collect();
    nary_mr(hasher, &refs)
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
    /// Authenticate the proof against a combined root at `tree_size`.
    ///
    /// Validates structure (canonical ordering, bounds, well-formed epochs,
    /// active set consistent with the timeline) and reconstructs the combined
    /// root via the canonicalization fold ([`combined_root`]) over the
    /// member-root children. On success both `active_roots` and `alg_epochs` are
    /// authenticated by the root.
    #[must_use]
    pub fn authenticate(
        &self,
        hasher: &dyn Hasher,
        tree_size: u64,
        arity: u64,
        expected_combined_root: &[u8],
        expected_active_algs: &[u64],
        config: VerifierConfig,
    ) -> bool {
        // Nothing is committed at size zero.
        if tree_size == 0 {
            return false;
        }
        if !ARITY_RANGE.contains(&arity) {
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

        // Reconstruct the combined root as the canonicalization fold over the
        // member-root children (plus the coverage child iff the activation is
        // non-trivial). The coverage child commits all algorithms' null runs,
        // derived from `alg_epochs` at `(tree_size, arity)`; if the presented
        // epochs imply different null runs than the committed structure, the
        // recomputed root will not match — so the activity the proof reads is
        // grounded in the committed runs. Genesis promotion is native: a single
        // member root under a trivial activation folds to itself.
        let computed = combined_root(
            hasher,
            &self.active_roots,
            &self.alg_epochs,
            tree_size,
            arity,
        );
        constant_time_eq(&computed, expected_combined_root)
    }

    /// Verify the coupling proof against a binding root for a given target algorithm.
    /// Returns the verified raw root hash for the target algorithm if successful.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn verify(
        &self,
        hasher: &dyn Hasher,
        target_alg_id: u64,
        tree_size: u64,
        arity: u64,
        combined_root: &[u8],
        expected_active_algs: &[u64],
        config: VerifierConfig,
    ) -> Option<Vec<u8>> {
        if !self.authenticate(
            hasher,
            tree_size,
            arity,
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

/// Helper wrapper demonstrating inclusion verification with decoupled coupling proofs.
///
/// `skeleton` is the structure's concrete inclusion topology for `index` —
/// supplied by the instantiation, not derived here, since the combinator lifts
/// both the append-only log (a mountain skeleton) and the mutable tree (a
/// rebalanced skeleton). The spine verifier pins `path` against it.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn verify_inclusion_with_coupling(
    hasher: &dyn Hasher,
    alg_id: u64,
    leaf_hash: &[u8],
    index: u64,
    tree_size: u64,
    arity: u64,
    skeleton: &[spine::SkeletonStep],
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
        arity,
        combined_root,
        expected_active_algs,
        config,
    ) {
        Some(r) => r,
        None => return false,
    };

    // One-directional inactive⇒N₀ check: if the committed activation marks
    // this position INACTIVE for alg_id, the leaf hash must equal the null
    // constant.  Active positions are unconstrained — a legitimate payload
    // `b"null"` hashes to null() but is never forbidden.  `None` (algorithm
    // not in the timeline at all) is rejected as an ill-formed proof. The
    // activity is sound because `coupling.verify` above pinned `alg_epochs` to
    // the committed null runs (equal-cover): a mismatched timeline would have
    // failed the binding-root recompute.
    match committed_active_at(&coupling.alg_epochs, alg_id, index) {
        Some(false) => {
            if !constant_time_eq(leaf_hash, &hasher.null()) {
                return false;
            }
        },
        Some(true) => {},
        None => return false,
    }

    verify_inclusion(hasher, leaf_hash, skeleton, path, &raw_root)
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
///
/// `skeleton` is the structure's concrete inclusion topology for `index` (see
/// [`verify_inclusion_with_coupling`]); it pins the null-leaf inclusion path when
/// the algorithm has a committed root. It is ignored for a frozen algorithm,
/// whose `path` must be empty.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn verify_inactivity_with_coupling(
    hasher: &dyn Hasher,
    alg_id: u64,
    index: u64,
    tree_size: u64,
    arity: u64,
    skeleton: &[spine::SkeletonStep],
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
        arity,
        combined_root,
        expected_active_algs,
        config,
    ) {
        return false;
    }

    // Position must be committed-inactive for this algorithm. Sound because the
    // authenticate above pinned `alg_epochs` to the committed null runs.
    match committed_active_at(&coupling.alg_epochs, alg_id, index) {
        Some(false) => {},
        _ => return false,
    }

    // If alg_id has an active committed root, open it with a null-leaf
    // inclusion proof.  If it is frozen (not in active_roots), the timeline
    // commitment alone is the evidence and the path must be empty.
    if let Some((_, raw_root)) = coupling.active_roots.iter().find(|&&(id, _)| id == alg_id) {
        verify_inclusion(hasher, &hasher.null(), skeleton, path, raw_root)
    } else {
        path.is_empty()
    }
}

/// The raw payload of an audit verification checkpoint.
///
/// This is the agnostic attestation payload: an out-of-band signer may sign
/// this struct to produce a checkpoint attestation, but the combinator never
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
    use sha2::{Digest, Sha256};

    use super::*;

    const MAX: u64 = u64::MAX;

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

    #[test]
    fn activation_trivial_is_informativeness_not_cardinality() {
        // No null run anywhere ⇒ trivial activation (no coverage child).
        assert!(null_runs_are_trivial(&[(0, vec![(0, MAX)])], 8, 2));
        // Many fully-active algorithms are still trivial — informativeness, not
        // registry cardinality.
        assert!(null_runs_are_trivial(
            &[
                (0, vec![(0, MAX)]),
                (1, vec![(0, MAX)]),
                (5, vec![(0, MAX)])
            ],
            8,
            2
        ));
        // A pre-activation prefix leaves null positions ⇒ non-trivial.
        assert!(!null_runs_are_trivial(&[(0, vec![(2, MAX)])], 8, 2));
        // A deactivation leaves null positions ⇒ non-trivial.
        assert!(!null_runs_are_trivial(&[(0, vec![(0, 5)])], 8, 2));
        // A gap-and-resume leaves a null run ⇒ non-trivial.
        assert!(!null_runs_are_trivial(&[(0, vec![(0, 3), (5, MAX)])], 8, 2));
        // Empty registry: vacuously trivial.
        assert!(null_runs_are_trivial(&[], 8, 2));
    }

    #[test]
    fn combined_root_is_the_fold_over_member_children() {
        let mr0 = vec![0xAA; 32];
        let mr1 = vec![0xBB; 32];
        let members = vec![(0u64, mr0.clone()), (1u64, mr1.clone())];
        // Fully-active activation: no coverage child, so the combined root is
        // exactly nary_mr over the two member roots — never a bespoke preimage.
        let trivial = vec![(0u64, vec![(0u64, MAX)]), (1, vec![(0, MAX)])];
        let got = combined_root(&H, &members, &trivial, 4, 2);
        let expected = nary_mr(&H, &[mr0.as_slice(), mr1.as_slice()]);
        assert_eq!(got, expected);
    }

    #[test]
    fn combined_root_singleton_promotes_with_no_predicate() {
        // One member root, fully active ⇒ nary_mr's len==1 arm promotes: the
        // combined root IS the member root, structurally (no special case).
        let mr0 = vec![0xCD; 32];
        let members = vec![(0u64, mr0.clone())];
        let got = combined_root(&H, &members, &[(0, vec![(0, MAX)])], 4, 2);
        assert_eq!(got, mr0);
    }

    #[test]
    fn combined_root_appends_coverage_child_iff_non_trivial() {
        let mr0 = vec![0x11; 32];
        let members = vec![(0u64, mr0.clone())];
        // A deactivation leaves null positions [5, 8): a coverage child
        // committing the null runs joins the fold, so the combined root is now a
        // genuine two-child node, NOT the bare member root.
        let non_trivial = vec![(0u64, vec![(0u64, 5u64)])];
        let got = combined_root(&H, &members, &non_trivial, 8, 2);
        let coverage = H.hash(&serialize_null_runs(&non_trivial, 8, 2));
        let expected = nary_mr(&H, &[mr0.as_slice(), coverage.as_slice()]);
        assert_eq!(got, expected);
        // And it differs from the fully-active (coverage-absent) encoding.
        assert_ne!(got, mr0);
        // Fully active over the same size yields no coverage child (back to the
        // bare promoted member root).
        let active = combined_root(&H, &members, &[(0, vec![(0, MAX)])], 8, 2);
        assert_eq!(active, mr0);
    }

    #[test]
    fn serialize_null_runs_is_injective_over_activation() {
        // Different null-run structures serialize differently; equal structures
        // serialize equally. The runs are derived from the epochs at (size, k).
        let a = serialize_null_runs(&[(0, vec![(0, MAX)])], 8, 2); // fully active
        let b = serialize_null_runs(&[(0, vec![(0, 4)])], 8, 2); // null [4,8)
        let c = serialize_null_runs(&[(0, vec![(0, 6)])], 8, 2); // null [6,8)
        assert_ne!(a, b);
        assert_ne!(b, c);
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

        // Alg 1's epoch closes exactly at 10, so it still covers position 9.
        assert_eq!(committed_active_algs(&timeline, 10), vec![0, 1]);
        // Position 4 falls in alg 0's gap [3, 5).
        assert_eq!(committed_active_algs(&timeline, 5), vec![1]);
        assert_eq!(committed_active_algs(&timeline, 2), vec![0, 1]);
        assert!(committed_active_algs(&timeline, 0).is_empty());
    }

    /// The soundness guard: the committed null runs ARE the activity source.
    /// Their span-union must equal the inactive position set exactly, so the
    /// active set — hence the epochs in canonical form — is recoverable as the
    /// complement. Committing the null runs commits the identical activity the
    /// intervals carry. Checked exhaustively over many timelines and arities.
    #[test]
    fn null_runs_cover_exactly_the_inactive_positions() {
        let active_at = |eps: &[(u64, u64)], i: u64| eps.iter().any(|&(s, e)| s <= i && i < e);
        let cases: Vec<Vec<(u64, u64)>> = vec![
            vec![(0, MAX)],               // fully active
            vec![(0, 0)],                 // fully inactive (genesis frozen)
            vec![(3, MAX)],               // pre-activation prefix
            vec![(0, 5)],                 // deactivated at 5
            vec![(0, 3), (5, MAX)],       // gap-and-resume
            vec![(0, 1), (2, 3), (4, 5)], // alternating
            vec![(2, 4), (7, 9)],         // two interior active runs
        ];
        for eps in &cases {
            for &tree_size in &[0u64, 1, 2, 3, 4, 7, 8, 9, 16, 27] {
                for &k in &[2u64, 3, 4] {
                    let runs = null_runs_for_alg(eps, tree_size, k);
                    // Reconstruct the inactive set from the runs and compare to
                    // the epochs' inactive set, position by position.
                    let mut covered = vec![false; tree_size as usize];
                    for r in &runs {
                        let span = k.pow(r.height);
                        // Every run must be aligned and within range.
                        assert_eq!(r.left % span, 0, "run not aligned: {r:?} k={k}");
                        assert!(r.left + span <= tree_size, "run overruns size: {r:?}");
                        for p in r.left..r.left + span {
                            assert!(!covered[p as usize], "runs overlap at {p}");
                            covered[p as usize] = true;
                        }
                    }
                    for i in 0..tree_size {
                        let active = active_at(eps, i);
                        assert_eq!(
                            covered[i as usize], !active,
                            "position {i} (eps={eps:?} size={tree_size} k={k}): null-run cover {} \
                             disagrees with inactive {}",
                            covered[i as usize], !active
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn null_runs_serialization_binds_arity_and_size() {
        // The serialized activation pins arity and tree_size, so the same runs
        // cannot be reinterpreted under a different spine.
        let eps = vec![(0u64, vec![(0u64, 4u64)])]; // inactive [4, size)
        let a = serialize_null_runs(&eps, 8, 2);
        let b = serialize_null_runs(&eps, 8, 4);
        let c = serialize_null_runs(&eps, 16, 2);
        assert_ne!(a, b);
        assert_ne!(a, c);
        // Trivial activation (fully active) serializes with zero algorithms and
        // is reported trivial.
        let triv = vec![(0u64, vec![(0u64, MAX)])];
        assert!(null_runs_are_trivial(&triv, 8, 2));
        assert!(!null_runs_are_trivial(&eps, 8, 2));
    }

    /// Reference oracle: the original position-by-position null-run computation.
    /// `null_runs_for_alg` feeds the binding-root preimage and every committed
    /// root, so any rewrite must be **byte-identical** to this scan. This is the
    /// independent definition the equivalence property checks against — kept
    /// inline so the property is its own byte-identity proof, not a tautology
    /// against the production code.
    fn null_runs_by_scan(eps: &[(u64, u64)], tree_size: u64, arity: u64) -> Vec<NullRun> {
        let active_at = |i: u64| eps.iter().any(|&(s, e)| s <= i && i < e);
        let mut runs = Vec::new();
        let mut i = 0u64;
        while i < tree_size {
            if active_at(i) {
                i += 1;
                continue;
            }
            let mut j = i;
            while j < tree_size && !active_at(j) {
                j += 1;
            }
            let mut left = i;
            while left < j {
                let mut height = 0u32;
                loop {
                    let next_h = height + 1;
                    let span = match arity.checked_pow(next_h) {
                        Some(s) => s,
                        None => break,
                    };
                    if left % span == 0 && left + span <= j {
                        height = next_h;
                    } else {
                        break;
                    }
                }
                runs.push(NullRun { left, height });
                left += arity.pow(height);
            }
            i = j;
        }
        runs
    }

    /// Byte-identity proof for the interval-wise `null_runs_for_alg`: across
    /// random epoch sets, tree sizes, and arities `k ∈ 2..=8`, the production
    /// function must equal the reference position-by-position scan exactly.
    ///
    /// `null_runs_for_alg` is a canonical function of `(eps, tree_size, arity)`
    /// whose output is the binding-root preimage; a rewrite that diverges on any
    /// input silently changes every committed root. Random epoch sets include
    /// unsorted, overlapping, empty, and out-of-bounds intervals — the function
    /// must agree with the scan on those too, since callers (and adversarial
    /// proptests) may present arbitrary epoch slices.
    #[test]
    fn null_runs_interval_wise_equals_position_scan() {
        // Inline xorshift64 PRNG: a deterministic broad sweep with no added
        // dependency. Seed fixed so failures are reproducible.
        let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };

        for _ in 0..50_000 {
            // Small tree sizes keep the scan oracle cheap while still exercising
            // multi-level aligned blocks (up to k^3 for k=2..8).
            let tree_size = next() % 130;
            let arity = 2 + next() % 7; // k ∈ 2..=8
            let n_eps = (next() % 5) as usize; // 0..=4 intervals, incl. empty set

            let mut eps: Vec<(u64, u64)> = Vec::with_capacity(n_eps);
            for _ in 0..n_eps {
                // Bias one in eight toward the open epoch end (u64::MAX) to cover
                // the fully-active / open-tail canonical forms.
                let start = next() % (tree_size + 1);
                let end = if next() % 8 == 0 {
                    MAX
                } else {
                    // Allow end < start (degenerate/empty) and end > tree_size
                    // (out of bounds): the scan ignores both, so the rewrite must.
                    next() % (tree_size + 2)
                };
                eps.push((start, end));
            }

            let scanned = null_runs_by_scan(&eps, tree_size, arity);
            let computed = null_runs_for_alg(&eps, tree_size, arity);
            assert_eq!(
                computed, scanned,
                "interval-wise null_runs_for_alg diverged from position scan: eps={eps:?} \
                 tree_size={tree_size} arity={arity}"
            );
        }

        // Explicit early-out witness: the fully-active canonical form yields no
        // runs (the O(1) path root() relies on).
        assert!(null_runs_for_alg(&[(0, MAX)], 1_000_000, 2).is_empty());
    }
}
