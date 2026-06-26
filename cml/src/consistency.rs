//! Consistency proof structure and verification — the append-only evolution
//! surface layered over the spine's inclusion proof.
//!
//! Inclusion, the proof step, and the canonical-encoding security boundary live
//! in the [`spine`] core and are re-exported here so a CML consumer reaches the
//! whole structural proof surface through `cml::proof::*`. This module owns only
//! what is append-only-specific and **epoch-free**: the [`ConsistencyProof`] (the
//! tree at `old_size` is a prefix of the tree at `new_size`).
//!
//! The *temporal* analog over the committed epoch timeline (`verify_epoch_evolution`)
//! and the coupling-wrapped consistency check are the `polydigest` combinator's
//! concern — they need the timeline, which the spine and CML do not see.

use spine::{ARITY_RANGE, Hasher, frontier_for_size};
// Re-export the spine proof surface so `cml::proof::*` reaches it while the
// originals live in `spine`. No parallels: these are the spine's, not copies.
pub use spine::{
    InclusionProof, ProofStep, constant_time_eq, reconstruct_inclusion_root, verify_inclusion,
    verify_inclusion_path_structure,
};

use crate::mountain::{bag_peaks, mountain_skeleton};

/// Consistency proof: proves tree at `old_size` is a prefix of tree at `new_size`.
///
/// MMR-native (increment-proof) shape: the old tree's rightmost peak is *included*
/// at one slot of the new tree's frontier, and the new frontier peaks bag to the
/// new root. Both authenticated roots are reconstructed from these fields plus the
/// trusted `(old_size, new_size, arity)`, reusing the same inclusion and peak-bag
/// primitives durability proves — no bespoke bisection trace, no coordinate map.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsistencyProof {
    /// The old tree's rightmost frontier node — its last (smallest) peak.
    pub boundary_hash: Vec<u8>,
    /// Inclusion path lifting `boundary_hash` to `new_peaks[split_index]`, the new
    /// frontier mountain that absorbed it. Its left-siblings are the older peaks
    /// that merged into that mountain; its right-siblings are the appended cells.
    pub peak_path: Vec<ProofStep>,
    /// The new tree's frontier peaks, left to right (`frontier_for_size` order).
    pub new_peaks: Vec<Vec<u8>>,
    /// The slot of the boundary peak's mountain in `new_peaks`.
    pub split_index: usize,
}

/// Verify a consistency proof.
///
/// Returns `true` if the proof demonstrates that the tree of size `old_size`
/// with root `old_root` is an append-only prefix of the tree of size `new_size`
/// with root `new_root` (arity `arity`).
///
/// # Trust contract (security-critical)
///
/// `old_size`, `new_size`, `arity`, `old_root`, and `new_root` are
/// **trusted parameters** and MUST come from an authenticated source — signed
/// Tree Heads (STHs) or trusted checkpoints — never from the proof or any
/// caller-untrusted input. The verifier reconstructs both roots from the sizes
/// and the proof fields (`boundary_hash`, `peak_path`, `new_peaks`,
/// `split_index`); if the sizes are attacker-controlled the append-only
/// guarantee is void.
///
/// Two further obligations follow from the length-hiding null-collapse design;
/// violating them defeats the guarantee even with a correct verifier:
///
/// * **Root equality stands in for tree equality only when the size is also bound.** All-null
///   (inactive) subtrees of *different* lengths share a root, so callers must never treat root
///   equality as "same tree" without pinning the corresponding size. This applies to caches, dedup,
///   and any comparison of stored/reconstructed roots.
/// * **The data-level guarantee needs *both* roots authenticated.** A `true` result binds the roots
///   (`old_root` is the genuine size-`old_size` prefix root of the size-`new_size` tree).
///   Concluding that the new *data* is a genuine extension of the old data holds only when
///   `new_root` is itself authenticated: a consistency proof carries perfect-subtree roots, not the
///   appended cells, and cannot witness an extension against an unauthenticated `new_root`.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn verify_consistency(
    hasher: &dyn Hasher,
    old_size: u64,
    new_size: u64,
    arity: u64,
    boundary_hash: &[u8],
    peak_path: &[ProofStep],
    new_peaks: &[Vec<u8>],
    split_index: usize,
    old_root: &[u8],
    new_root: &[u8],
) -> bool {
    reconstruct_consistency_roots(
        hasher,
        old_size,
        new_size,
        arity,
        boundary_hash,
        peak_path,
        new_peaks,
        split_index,
    )
    .is_some_and(|(computed_old, computed_new)| {
        constant_time_eq(&computed_old, old_root) & constant_time_eq(&computed_new, new_root)
    })
}

/// Reconstruct the old and new raw roots from a consistency proof.
///
/// Building block for [`verify_consistency`]; it computes both roots but does
/// not compare them to trusted ones. Callers must hold to the same trust
/// contract: `old_size`, `new_size`, and `arity` must be authenticated, and
/// the returned roots are only meaningful when checked against authenticated
/// roots with the matching sizes bound (see [`verify_consistency`] for the
/// length-binding and both-roots-authenticated obligations).
///
/// The reconstruction is purely *inclusion + peak-bag*:
///
/// 1. `boundary_hash` is lifted through `peak_path` to `new_peaks[split_index]` by
///    [`reconstruct_inclusion_root`], pinned by the boundary mountain's slice of
///    [`mountain_skeleton`]; the result must equal that peak.
/// 2. the new root is [`bag_peaks`] over `new_peaks`.
/// 3. the old root is [`bag_peaks`] over the old frontier peaks: the shared peaks left of the
///    boundary mountain (`new_peaks[..split_index]`), the older peaks that merged into it (the
///    left-siblings along `peak_path`, gathered highest-mountain first to match frontier order),
///    and `boundary_hash` last.
///
/// Every old peak is therefore an *authenticated* slice of the inclusion proof or
/// `new_peaks`, so a `true` consistency result binds the old root with no extra
/// trusted state beyond the two roots.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn reconstruct_consistency_roots(
    hasher: &dyn Hasher,
    old_size: u64,
    new_size: u64,
    arity: u64,
    boundary_hash: &[u8],
    peak_path: &[ProofStep],
    new_peaks: &[Vec<u8>],
    split_index: usize,
) -> Option<(Vec<u8>, Vec<u8>)> {
    let digest_len = hasher.empty().len();
    if digest_len == 0 || digest_len > 64 {
        return None;
    }
    if boundary_hash.len() != digest_len {
        return None;
    }
    if old_size == 0 || old_size >= new_size {
        return None;
    }
    if !ARITY_RANGE.contains(&arity) {
        return None;
    }

    let k = arity;
    let old_coords = frontier_for_size(old_size, k);
    let new_coords = frontier_for_size(new_size, k);

    let &(boundary_left, boundary_height) = old_coords.last()?;

    // `new_peaks` must be the new tree's frontier (bound to the trusted `new_size`)
    // and every peak the right digest width, or the bag is meaningless.
    if new_peaks.len() != new_coords.len() {
        return None;
    }
    if split_index >= new_coords.len() {
        return None;
    }
    if new_peaks.iter().any(|p| p.len() != digest_len) {
        return None;
    }

    // The boundary peak must actually fall inside the mountain it claims.
    let (new_left, new_height) = new_coords[split_index];
    let cap = k.checked_pow(new_height)?;
    let limit = new_left.checked_add(cap)?;
    if boundary_left < new_left || boundary_left >= limit {
        return None;
    }
    if new_height < boundary_height {
        return None;
    }

    // 1. Inclusion of the boundary peak at `new_peaks[split_index]`.
    //
    // The boundary node sits at height `boundary_height`; its path to the mountain
    // peak climbs heights `[boundary_height, new_height)`. That is exactly the
    // upper portion of the mountain's leaf → peak skeleton — the leaf-aligned
    // boundary subtree contributes the low `boundary_height` (all-zero) digits, so
    // the climb is the skeleton slice past them. The bag steps above the peak are
    // excluded: this proves inclusion *at the peak*, not at the root.
    let full_skeleton = mountain_skeleton(k, new_size, boundary_left)?;
    let bh = boundary_height as usize;
    let nh = new_height as usize;
    if full_skeleton.len() < nh {
        return None;
    }
    let climb = &full_skeleton[bh..nh];
    if peak_path.len() != climb.len() {
        return None;
    }
    let recovered = reconstruct_inclusion_root(hasher, boundary_hash, climb, peak_path)?;
    if !constant_time_eq(&recovered, &new_peaks[split_index]) {
        return None;
    }

    // 2. The new root is the bag of the new frontier peaks (unchanged fold).
    let computed_new_root = bag_peaks(hasher, new_peaks, k);

    // 3. The old root is the bag of the old frontier peaks. They are, in frontier
    // (decreasing-height) order: the peaks left of the boundary mountain — shared
    // verbatim with the new tree — then the older peaks that merged into the
    // boundary mountain, then the boundary peak itself. The merged peaks are the
    // left-siblings along the climb: at each step the children before the path
    // node lie wholly within the old tree (the right-siblings are appended cells).
    // Climbing runs boundary → peak (lowest height first), so iterate `peak_path`
    // in reverse to take the highest mountains first and preserve frontier order.
    let mut old_peaks: Vec<Vec<u8>> = new_peaks[..split_index].to_vec();
    for step in peak_path.iter().rev() {
        let left = step.position.min(step.siblings.len());
        for sib in &step.siblings[..left] {
            old_peaks.push(sib.clone());
        }
    }
    old_peaks.push(boundary_hash.to_vec());
    let computed_old_root = bag_peaks(hasher, &old_peaks, k);

    Some((computed_old_root, computed_new_root))
}
