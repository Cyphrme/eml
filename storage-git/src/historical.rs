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

/// Reconstruct `C(n)` from the current checkpoint tree (`current_tree` at
/// `current_size` items) and write it, returning its object id. `n` must be
/// `<= current_size`; the caller checks range and the `n == current_size`
/// fast path. `hashers` are the caller-registered folds (SG26 -- opaque
/// trait objects, no algorithm named by this crate) `roots/` needs.
pub(crate) fn reconstruct(
    repo: &gix::Repository,
    arity: u64,
    current_tree: Option<ObjectId>,
    current_size: u64,
    kind_byte: u8,
    n: u64,
    hashers: &HashMap<u64, Box<dyn Hasher>>,
) -> Result<ObjectId, Error> {
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

    let meta_blob = gitutil::write_blob(repo, &layout::encode_meta(arity, n, kind_byte))?;
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
/// algorithm this instance has a registered [`spine::Hasher`] for, active
/// at `n` (per `projected_epochs`, SG13), fold that algorithm's frontier
/// peak digests -- read back from the already-resolved peak objects in
/// `resolved_by_coord` -- into the member root via [`bag_peaks`], mirroring
/// `cml::engine::compute_root`'s write-time computation exactly (same
/// fold, same null-substitution rule as `get_node_hash`,
/// `cml/src/engine.rs:262-298`). An active algorithm absent from `hashers`
/// is omitted, matching SG14's "no entry for an algorithm not active at
/// n" shape by simply never producing the entry this crate cannot compute.
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
    // rather than folded.
    if target_coords.is_empty() {
        return gitutil::write_tree(repo, Vec::new());
    }

    let mut entries = Vec::new();
    for (&alg_id, hasher) in hashers {
        let Some(projected) = projected_epochs.get(&alg_id) else {
            continue;
        };
        if !layout::is_active_at(projected) {
            continue;
        }

        let mut peak_digests = Vec::with_capacity(target_coords.len());
        for &(left, height) in target_coords {
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
                let peak_id = *resolved_by_coord.get(&(left, height)).ok_or_else(|| {
                    corrupt(format!(
                        "no resolved peak for (left={left}, height={height})"
                    ))
                })?;
                let digest_tree = gitutil::find_entry(repo, peak_id, "digest")?;
                let blob_id = match digest_tree {
                    Some(d) => gitutil::find_entry(repo, d, &layout::hex16(alg_id))?,
                    None => None,
                };
                match blob_id {
                    Some(b) => gitutil::read_blob(repo, b)?,
                    None => {
                        return Err(corrupt(format!(
                            "algorithm {alg_id} active over (left={left}, height={height}) but \
                             its peak carries no digest/{} entry (SG3)",
                            layout::hex16(alg_id)
                        )));
                    },
                }
            } else {
                hasher.null()
            };
            peak_digests.push(digest);
        }

        let root = bag_peaks(hasher.as_ref(), &peak_digests, arity);
        let blob_id = gitutil::write_blob(repo, &root)?;
        entries.push(entry(EntryKind::Blob, layout::hex16(alg_id), blob_id));
    }
    gitutil::write_tree(repo, entries)
}
