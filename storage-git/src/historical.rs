//! `tree_at(n)` (§4.3, SG20): reconstructing a past checkpoint tree from the
//! current one.
//!
//! `roots/` at a historical `n < size` needs a past member root, which needs
//! the algorithm's hash fold over its frontier peaks as they stood at `n`
//! (`cml::mountain::bag_peaks`, the same fold `cml::engine::compute_root`
//! uses to produce the live root this layer stores verbatim). This crate
//! still never names or assumes a specific algorithm (SG26): the fold runs
//! under a `spine::Hasher` trait object the *caller* registers per `alg_id`
//! via [`crate::GitStorage::register_hasher`] -- an opaque interface keyed
//! by the same opaque `alg_id` every other method already treats it as.
//! Every other input this fold needs (the frontier peak digests, the
//! algorithm's active range at `n`) is already reconstructed here from the
//! object database and `epochs/`'s own truncation, so the fold reproduces
//! the exact bytes `C(n)` was originally written with (SG9 purity), making
//! `tree_at(n)`'s object byte-identical to that original checkpoint.
//!
//! An algorithm active at `n` with no hasher registered omits its
//! `roots/hex(alg_id,16)` entry -- the crate's previous unconditional
//! departure, now opt-out per algorithm rather than universal. See this
//! crate's top-level docs for the full writeup.

use std::collections::HashMap;

use cml::mountain::bag_peaks;
use gix::ObjectId;
use gix::objs::tree::EntryKind;
use spine::{Hasher, frontier_for_size};

use crate::error::GitStorageError as Error;
use crate::gitutil::{self, entry};
use crate::layout::{self, hex2};
use crate::read;

fn corrupt(msg: impl Into<String>) -> Error {
    Error::Corruption(msg.into())
}

/// One algorithm's projected epoch history at a given size (§3.2, SG13),
/// keyed by `alg_id`. Named so `reconstruct_epochs`/`reconstruct_roots`
/// don't repeat the nested collection type at every call site.
type EpochsByAlg = HashMap<u64, Vec<(u64, u64)>>;

/// This instance's current committed state, bundled only to stay under
/// clippy's too-many-arguments threshold -- every field is a distinct fact
/// [`reconstruct`] projects into the historical `meta` it builds (`tree`
/// and `size` also drive the reconstruction itself), never a single
/// concept split apart.
#[derive(Clone, Copy)]
pub(crate) struct CurrentState {
    pub tree: Option<ObjectId>,
    pub size: u64,
    pub kind_byte: u8,
    /// This log's own committed resume boundary (GB44, §4.3's SG20
    /// amendment; `None` for a log never resumed), carried into the
    /// reconstructed `meta` unchanged -- it is a fact about the log's
    /// provenance, not about which historical `n` is being asked for.
    pub resume_boundary: Option<u64>,
}

/// Reconstruct `C(n)` from the current checkpoint tree and write it,
/// returning its object id. `n` must be `<= current.size`; the caller
/// checks range and the `n == current.size` fast path. `hashers` are the
/// caller-registered folds (SG26 -- opaque trait objects, no algorithm
/// named by this crate) `roots/` needs.
pub(crate) fn reconstruct(
    repo: &gix::Repository,
    arity: u64,
    current: CurrentState,
    n: u64,
    hashers: &HashMap<u64, Box<dyn Hasher>>,
) -> Result<ObjectId, Error> {
    let CurrentState {
        tree: current_tree,
        size: current_size,
        kind_byte,
        resume_boundary,
    } = current;
    let target_coords = frontier_for_size(n, arity);
    let current_coords = frontier_for_size(current_size, arity);

    let mut resolved: Vec<((u64, u32), ObjectId)> = Vec::with_capacity(target_coords.len());
    for &(left, height) in &target_coords {
        let id = resolve_historical_node(repo, arity, current_tree, &current_coords, left, height)?;
        resolved.push(((left, height), id));
    }
    let resolved_by_coord: HashMap<(u64, u32), ObjectId> = resolved.iter().copied().collect();

    let mut by_height: HashMap<u32, Vec<(u64, ObjectId)>> = HashMap::new();
    for &((left, height), id) in &resolved {
        by_height.entry(height).or_default().push((left, id));
    }
    let mut peaks_top = Vec::with_capacity(by_height.len());
    for (height, mut lefts) in by_height {
        lefts.sort_unstable_by_key(|&(l, _)| l);
        let group: Vec<_> = lefts
            .into_iter()
            .enumerate()
            .map(|(q, (_, id))| entry(EntryKind::Tree, hex2(q as u64), id))
            .collect();
        let group_tree = gitutil::write_tree(repo, group)?;
        peaks_top.push(entry(EntryKind::Tree, hex2(u64::from(height)), group_tree));
    }
    let peaks_tree = gitutil::write_tree(repo, peaks_top)?;

    let (epochs_tree, projected_epochs) = reconstruct_epochs(repo, current_tree, n)?;
    let roots_tree = reconstruct_roots(
        repo,
        arity,
        &target_coords,
        &resolved_by_coord,
        &projected_epochs,
        hashers,
    )?;

    let meta_blob = gitutil::write_blob(
        repo,
        &layout::encode_meta(arity, n, kind_byte, resume_boundary),
    )?;
    let top = vec![
        entry(EntryKind::Blob, "meta", meta_blob),
        entry(EntryKind::Tree, "epochs", epochs_tree),
        entry(EntryKind::Tree, "roots", roots_tree),
        entry(EntryKind::Tree, "peaks", peaks_tree),
    ];
    gitutil::write_tree(repo, top)
}

fn resolve_historical_node(
    repo: &gix::Repository,
    arity: u64,
    current_tree: Option<ObjectId>,
    current_coords: &[(u64, u32)],
    left: u64,
    height: u32,
) -> Result<ObjectId, Error> {
    let current_tree =
        current_tree.ok_or_else(|| corrupt("no current checkpoint tree to reconstruct from"))?;

    if let Some(idx) = current_coords.iter().position(|&c| c == (left, height)) {
        return read::peak_object_id(repo, current_tree, current_coords, idx);
    }
    if let Some(idx) = covering_peak(current_coords, arity, left, height) {
        let (peak_left, peak_height) = current_coords[idx];
        let peak_id = read::peak_object_id(repo, current_tree, current_coords, idx)?;
        if let Some(id) = descend(repo, arity, peak_left, peak_height, peak_id, left, height)? {
            return Ok(id);
        }
    }
    Err(corrupt(format!(
        "historical coordinate (left={left}, height={height}) is not reconstructable: it was \
         sealed opaque and has since been folded into a taller peak"
    )))
}

// Re-implemented rather than made `pub(crate)` in `read.rs` to keep that
// module's surface scoped to the live-tree read path; both copies are exact
// mirrors of the same §2.4 algorithm and are exercised by the same
// differential tests.
fn covering_peak(coords: &[(u64, u32)], arity: u64, left: u64, height: u32) -> Option<usize> {
    let cap = arity.checked_pow(height)?;
    let end = left.checked_add(cap)?;
    coords.iter().position(|&(pl, ph)| {
        let pcap = arity.pow(ph);
        left >= pl && end <= pl + pcap
    })
}

fn descend(
    repo: &gix::Repository,
    arity: u64,
    peak_left: u64,
    peak_height: u32,
    peak_id: ObjectId,
    target_left: u64,
    target_height: u32,
) -> Result<Option<ObjectId>, Error> {
    let mut cur_left = peak_left;
    let mut cur_height = peak_height;
    let mut cur_id = peak_id;
    while cur_height > target_height {
        let span = arity.pow(cur_height - 1);
        let child_idx = (target_left - cur_left) / span;
        let Some(child_id) = gitutil::find_entry(repo, cur_id, &hex2(child_idx))? else {
            return Ok(None);
        };
        cur_id = child_id;
        cur_left += child_idx * span;
        cur_height -= 1;
    }
    Ok(Some(cur_id))
}

/// Reconstruct `epochs/` (§3.2, SG13) and return the per-algorithm
/// projected epoch history at `n` alongside it, so [`reconstruct_roots`]
/// judges activity from *exactly* the same truncation `epochs/` itself
/// commits (never a separately-recomputed, potentially divergent view).
fn reconstruct_epochs(
    repo: &gix::Repository,
    current_tree: Option<ObjectId>,
    n: u64,
) -> Result<(ObjectId, EpochsByAlg), Error> {
    let Some(current_tree) = current_tree else {
        return Ok((gitutil::write_tree(repo, Vec::new())?, HashMap::new()));
    };
    let metas = read::load_algorithm_metas(repo, current_tree)?;
    let mut entries = Vec::with_capacity(metas.len());
    let mut projected_by_alg = HashMap::with_capacity(metas.len());
    for (alg_id, history) in metas {
        if let Some(projected) = layout::epochs_at(&history, n) {
            let blob_id = gitutil::write_blob(repo, &layout::encode_epochs(&projected))?;
            entries.push(entry(EntryKind::Blob, layout::hex16(alg_id), blob_id));
            projected_by_alg.insert(alg_id, projected);
        }
    }
    Ok((gitutil::write_tree(repo, entries)?, projected_by_alg))
}

/// Reconstruct `roots/` (§3.3, SG14) at a historical `n`: for every
/// algorithm active at `n` (per `projected_epochs`, SG13), fold that
/// algorithm's frontier peak digests -- read back from the already-resolved
/// peak objects in `resolved_by_coord` -- into the member root via
/// [`fold_root`], mirroring `cml::engine::compute_root`'s write-time
/// computation exactly (same fold, same null-substitution rule as
/// `get_node_hash`, `cml/src/engine.rs:262-298`).
///
/// SG20's amendment (GB44): an algorithm active at `n` with **no** hasher
/// in `hashers` is no longer silently omitted -- `tree_at` MUST never
/// return a tree other than `C(n)` (SGG12), and an omitted `roots/` entry
/// for an algorithm the log actually has one for is exactly that: a
/// well-formed but wrong tree. This returns an error naming the algorithm
/// instead.
fn reconstruct_roots(
    repo: &gix::Repository,
    arity: u64,
    target_coords: &[(u64, u32)],
    resolved_by_coord: &HashMap<(u64, u32), ObjectId>,
    projected_epochs: &EpochsByAlg,
    hashers: &HashMap<u64, Box<dyn Hasher>>,
) -> Result<ObjectId, Error> {
    // n=0: the frontier is empty (no item has ever been appended), so no
    // algorithm -- however "active" its registration epoch already reads --
    // has ever had `NaryMerkleLog::build_append_state` actually compute and
    // hand this layer a `checkpoint_roots` value (that only happens inside
    // an append). The live `C(0)` this crate itself writes for a freshly
    // registered algorithm therefore carries no `roots/` entry at all
    // (`build_roots` starts from an empty carry-forward map and no append
    // has ever overlaid a value onto it); reconstructing a fabricated
    // `bag_peaks` root over an empty peak set here would diverge from that
    // genuinely-written object, so this one-time bootstrap state is named
    // rather than folded, and no hasher is required for it either.
    if target_coords.is_empty() {
        return gitutil::write_tree(repo, Vec::new());
    }

    let mut entries = Vec::new();
    for (&alg_id, projected) in projected_epochs {
        if !layout::is_active_at(projected) {
            continue;
        }
        let hasher = hashers.get(&alg_id).ok_or_else(|| {
            corrupt(format!(
                "tree_at: algorithm {alg_id} is active at this historical size but has no hasher \
                 registered (register_hasher, SG20 amendment, GB44) -- a historical roots/{} \
                 entry cannot be reconstructed without one",
                layout::hex16(alg_id)
            ))
        })?;

        let root = fold_root(
            repo,
            arity,
            target_coords,
            projected,
            hasher.as_ref(),
            alg_id,
            |left, height| {
                resolved_by_coord
                    .get(&(left, height))
                    .copied()
                    .ok_or_else(|| {
                        corrupt(format!(
                            "no resolved peak for (left={left}, height={height})"
                        ))
                    })
            },
        )?;
        let blob_id = gitutil::write_blob(repo, &root)?;
        entries.push(entry(EntryKind::Blob, layout::hex16(alg_id), blob_id));
    }
    gitutil::write_tree(repo, entries)
}

/// Fold `hasher`'s digests over `coords`' peaks into one member root via
/// [`bag_peaks`], resolving each peak's object id through `peak_id`. Shared
/// by [`reconstruct_roots`] (peaks freshly resolved into a caller-owned
/// map) and [`validate_hashers`] (peaks read directly off the current,
/// already-committed tree) so both fold the identical algorithm (SG20
/// amendment).
fn fold_root<F>(
    repo: &gix::Repository,
    arity: u64,
    coords: &[(u64, u32)],
    projected: &[(u64, u64)],
    hasher: &dyn Hasher,
    alg_id: u64,
    mut peak_id: F,
) -> Result<Vec<u8>, Error>
where
    F: FnMut(u64, u32) -> Result<ObjectId, Error>,
{
    let mut peak_digests = Vec::with_capacity(coords.len());
    for &(left, height) in coords {
        let cap = arity.checked_pow(height).ok_or_else(|| {
            corrupt(format!(
                "(left={left}, height={height}): arity^height overflows u64"
            ))
        })?;
        let limit = left.checked_add(cap).ok_or_else(|| {
            corrupt(format!(
                "(left={left}, height={height}): left+span overflows u64"
            ))
        })?;
        let active = projected
            .iter()
            .any(|&(start, end)| start < limit && end > left);
        let digest = if active {
            let id = peak_id(left, height)?;
            let digest_tree = gitutil::find_entry(repo, id, "digest")?;
            let blob_id = match digest_tree {
                Some(d) => gitutil::find_entry(repo, d, &layout::hex16(alg_id))?,
                None => None,
            };
            match blob_id {
                Some(b) => gitutil::read_blob(repo, b)?,
                None => {
                    return Err(corrupt(format!(
                        "algorithm {alg_id} active over (left={left}, height={height}) but its \
                         peak carries no digest/{} entry (SG3)",
                        layout::hex16(alg_id)
                    )));
                },
            }
        } else {
            hasher.null()
        };
        peak_digests.push(digest);
    }
    Ok(bag_peaks(hasher, &peak_digests, arity))
}

/// Reject a registered hasher before any historical root is trusted (§4.3,
/// SG20 amendment; GB44): "A registered hasher must be checked against the
/// stored current root ... before any historical root is trusted."
///
/// [`bag_peaks`] promotes a lone peak to itself (`cml::mountain::bag_peaks`
/// doc comment), so folding across the *current* frontier's peaks is
/// uninformative whenever that frontier happens to be a single peak -- the
/// wrong hasher is never actually invoked. This instead recomputes each
/// currently active, fully-covered peak's **own** digest bottom-up from its
/// materialized structure (`Hasher::leaf`/`Hasher::node`, the same
/// operations that produced the stored value) and compares the result
/// against the digest this layer already has on file for that exact
/// coordinate -- exercising the hasher's real behavior regardless of how
/// many peaks the current frontier has. A node this cannot fully recompute
/// (opaque somewhere along the way, or the algorithm's activity does not
/// cover the node's whole span) is skipped -- best effort, matching this
/// crate's other named departures rather than guessing at `cml`'s
/// null-substitution rule for partial coverage.
pub(crate) fn validate_hashers(
    repo: &gix::Repository,
    arity: u64,
    current_tree: ObjectId,
    current_size: u64,
    hashers: &HashMap<u64, Box<dyn Hasher>>,
) -> Result<(), Error> {
    if hashers.is_empty() {
        return Ok(());
    }
    let current_coords = frontier_for_size(current_size, arity);
    let metas = read::load_algorithm_metas(repo, current_tree)?;

    for (&alg_id, hasher) in hashers {
        let Some((_, history)) = metas.iter().find(|(id, _)| *id == alg_id) else {
            continue; // never registered on this log at all -- nothing to check against
        };
        let Some(projected) = layout::epochs_at(history, current_size) else {
            continue;
        };
        if !layout::is_active_at(&projected) {
            continue; // frozen/removed already -- no live peak to recompute from
        }

        for &(left, height) in &current_coords {
            let cap = arity.pow(height);
            let fully_covered = projected
                .iter()
                .any(|&(start, end)| start <= left && end >= left + cap);
            if !fully_covered {
                continue;
            }
            let idx = current_coords
                .iter()
                .position(|&c| c == (left, height))
                .expect("left/height came from current_coords itself");
            let peak_id = read::peak_object_id(repo, current_tree, &current_coords, idx)?;
            let Some(recomputed) = recompute_digest(repo, arity, peak_id, height, hasher.as_ref())?
            else {
                continue;
            };
            let Some(digest_tree) = gitutil::find_entry(repo, peak_id, "digest")? else {
                continue;
            };
            let Some(stored_id) = gitutil::find_entry(repo, digest_tree, &layout::hex16(alg_id))?
            else {
                continue;
            };
            let stored = gitutil::read_blob(repo, stored_id)?;
            if recomputed != stored {
                return Err(corrupt(format!(
                    "tree_at: the hasher registered for algorithm {alg_id} does not reproduce the \
                     digest already stored at (left={left}, height={height}) (SG20 amendment, \
                     GB44) -- a wrong or mismatched hasher must be rejected before any historical \
                     root is trusted"
                )));
            }
        }
    }
    Ok(())
}

/// Recompute a materialized node's digest bottom-up with `hasher`
/// (`Hasher::leaf` at the leaves, `Hasher::node` at every merge), or `None`
/// if the node -- or any descendant along the way -- is opaque: nothing to
/// recompute from, so [`validate_hashers`] has no ground truth here and
/// skips it rather than guessing.
fn recompute_digest(
    repo: &gix::Repository,
    arity: u64,
    node_id: ObjectId,
    height: u32,
    hasher: &dyn Hasher,
) -> Result<Option<Vec<u8>>, Error> {
    if height == 0 {
        return match gitutil::find_entry(repo, node_id, "leaf")? {
            Some(leaf_id) => Ok(Some(hasher.leaf(&gitutil::read_blob(repo, leaf_id)?))),
            None => Ok(None),
        };
    }
    let mut children = Vec::with_capacity(arity as usize);
    for c in 0..arity {
        let Some(child_id) = gitutil::find_entry(repo, node_id, &hex2(c))? else {
            return Ok(None);
        };
        let Some(digest) = recompute_digest(repo, arity, child_id, height - 1, hasher)? else {
            return Ok(None);
        };
        children.push(digest);
    }
    let refs: Vec<&[u8]> = children.iter().map(Vec::as_slice).collect();
    Ok(Some(hasher.node(&refs)))
}
