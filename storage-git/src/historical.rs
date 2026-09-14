//! `tree_at(n)` (§4.3, SG20): reconstructing a past checkpoint tree from the
//! current one.
//!
//! `roots/` at a historical `n < size` is a named departure, not silently
//! dropped: recomputing a past member root needs the algorithm's hash fold
//! over its frontier peaks (`spine::nary_mr`/`bag_peaks`), and this crate
//! deliberately never links against a hash implementation (SG26) or holds a
//! `spine::Hasher`. A live root is *given* to this layer via
//! `checkpoint_roots`; a past one that has since been superseded was never
//! retained anywhere this layer's own object model can address (SG1's fixed
//! four top-level entries leave no room for a size-indexed root history).
//! `meta`/`epochs`/`peaks` are fully reconstructed; `roots/` at a historical
//! `n` is the empty tree. See this crate's top-level docs for the complete
//! departure writeup.

use gix::ObjectId;
use gix::objs::tree::EntryKind;
use spine::frontier_for_size;

use crate::error::GitStorageError as Error;
use crate::gitutil::{self, entry};
use crate::layout::{self, hex2};
use crate::read;

fn corrupt(msg: impl Into<String>) -> Error {
    Error::Corruption(msg.into())
}

/// Reconstruct `C(n)` from the current checkpoint tree (`current_tree` at
/// `current_size` items) and write it, returning its object id. `n` must be
/// `<= current_size`; the caller checks range and the `n == current_size`
/// fast path.
pub(crate) fn reconstruct(
    repo: &gix::Repository,
    arity: u64,
    current_tree: Option<ObjectId>,
    current_size: u64,
    kind_byte: u8,
    n: u64,
) -> Result<ObjectId, Error> {
    let target_coords = frontier_for_size(n, arity);
    let current_coords = frontier_for_size(current_size, arity);

    let mut resolved: Vec<((u64, u32), ObjectId)> = Vec::with_capacity(target_coords.len());
    for &(left, height) in &target_coords {
        let id = resolve_historical_node(repo, arity, current_tree, &current_coords, left, height)?;
        resolved.push(((left, height), id));
    }

    let mut by_height: std::collections::HashMap<u32, Vec<(u64, ObjectId)>> = std::collections::HashMap::new();
    for ((left, height), id) in resolved {
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

    let epochs_tree = reconstruct_epochs(repo, current_tree, n)?;
    // Named departure (module docs): a superseded historical root cannot be
    // recomputed without a hasher, so the reconstructed roots/ is empty.
    let roots_tree = gitutil::write_tree(repo, Vec::new())?;

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
    let current_tree = current_tree.ok_or_else(|| corrupt("no current checkpoint tree to reconstruct from"))?;

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

fn reconstruct_epochs(repo: &gix::Repository, current_tree: Option<ObjectId>, n: u64) -> Result<ObjectId, Error> {
    let Some(current_tree) = current_tree else {
        return gitutil::write_tree(repo, Vec::new());
    };
    let metas = read::load_algorithm_metas(repo, current_tree)?;
    let mut entries = Vec::with_capacity(metas.len());
    for (alg_id, history) in metas {
        if let Some(projected) = layout::epochs_at(&history, n) {
            let blob_id = gitutil::write_blob(repo, &layout::encode_epochs(&projected))?;
            entries.push(entry(EntryKind::Blob, layout::hex16(alg_id), blob_id));
        }
    }
    gitutil::write_tree(repo, entries)
}
