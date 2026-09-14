//! Position-lookup reads (§2.4, SG8) against an arbitrary checkpoint tree:
//! shared by the live staged-tree reads (`Storage::get_leaf`/`get_node`) and
//! [`crate::GitStorage::open_at`]'s read-only view.
//!
//! Scope, named rather than silently assumed: this walks from a peak down
//! through `hex(c,2)` children, so it resolves any coordinate that is either
//! a current peak itself or a descendant of a **materialized** peak. A
//! coordinate that was sealed opaque (§2.6) and has since been folded into a
//! taller peak has no reachable path here -- SG4/SG10 forbid an opaque node
//! from carrying `hex(c,2)` children at all, so nothing below a taller
//! opaque peak is addressable once it stops being the frontier's own peak.
//! `get_node` and `tree_at` both report this honestly (`Ok(None)` / a
//! reconstruction error) rather than fabricating a value; see this crate's
//! top-level docs for the full departure writeup.

use gix::ObjectId;
use spine::frontier_for_size;

use crate::error::GitStorageError as Error;
use crate::gitutil;
use crate::layout::{hex2, hex16};

fn corrupt(msg: impl Into<String>) -> Error {
    Error::Corruption(msg.into())
}

/// The object id of the `peaks/hex(j,2)/hex(q,2)` entry for `coords[target]`.
pub(crate) fn peak_object_id(
    repo: &gix::Repository,
    tree_id: ObjectId,
    coords: &[(u64, u32)],
    target: usize,
) -> Result<ObjectId, Error> {
    let (_, height) = coords[target];
    let q = coords[..target].iter().filter(|&&(_, h)| h == height).count();
    let peaks_id = gitutil::find_entry(repo, tree_id, "peaks")?.ok_or_else(|| corrupt("C(n) missing peaks/"))?;
    let group_id = gitutil::find_entry(repo, peaks_id, &hex2(u64::from(height)))?
        .ok_or_else(|| corrupt(format!("missing peaks/{}", hex2(u64::from(height)))))?;
    gitutil::find_entry(repo, group_id, &hex2(q as u64))?
        .ok_or_else(|| corrupt(format!("missing peaks/{}/{}", hex2(u64::from(height)), hex2(q as u64))))
}

/// Descend from a peak at `(peak_left, peak_height)` down to
/// `(target_left, target_height)`, or `Ok(None)` if some ancestor along the
/// way is opaque (no `hex(c,2)` children to descend through).
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

/// Find the frontier coordinate at `size` covering `(left, height)`, i.e.
/// the peak whose aligned block `[peak_left, peak_left + k^peak_height)`
/// contains `[left, left + k^height)`.
fn covering_peak(coords: &[(u64, u32)], arity: u64, left: u64, height: u32) -> Option<usize> {
    let cap = arity.checked_pow(height)?;
    let end = left.checked_add(cap)?;
    coords.iter().position(|&(pl, ph)| {
        let pcap = arity.pow(ph);
        left >= pl && end <= pl + pcap
    })
}

/// Read item `index`'s raw leaf payload out of the checkpoint tree at
/// `tree_id` (currently `size` items).
pub(crate) fn get_leaf(
    repo: &gix::Repository,
    tree_id: ObjectId,
    arity: u64,
    size: u64,
    index: u64,
) -> Result<Vec<u8>, Error> {
    if index >= size {
        return Err(Error::NotFound(format!("leaf index {index} (size {size})")));
    }
    let coords = frontier_for_size(size, arity);
    let target = covering_peak(&coords, arity, index, 0)
        .ok_or_else(|| corrupt(format!("no frontier peak covers leaf index {index} at size {size}")))?;
    let (peak_left, peak_height) = coords[target];
    let peak_id = peak_object_id(repo, tree_id, &coords, target)?;
    let node_id = descend(repo, arity, peak_left, peak_height, peak_id, index, 0)?
        .ok_or_else(|| Error::NotFound(format!("leaf {index} is not materialized (opaque ancestor)")))?;
    match gitutil::find_entry(repo, node_id, "leaf")? {
        Some(blob_id) => gitutil::read_blob(repo, blob_id),
        None => Err(Error::NotFound(format!("leaf {index} was never given (no leaf blob)"))),
    }
}

/// Read a sealed node digest at `(alg_id, left, height)` out of the
/// checkpoint tree at `tree_id` (currently `size` items).
pub(crate) fn get_node(
    repo: &gix::Repository,
    tree_id: ObjectId,
    arity: u64,
    size: u64,
    alg_id: u64,
    left: u64,
    height: u32,
) -> Result<Option<Vec<u8>>, Error> {
    let coords = frontier_for_size(size, arity);
    let Some(target) = covering_peak(&coords, arity, left, height) else {
        return Ok(None);
    };
    let (peak_left, peak_height) = coords[target];
    let peak_id = peak_object_id(repo, tree_id, &coords, target)?;
    let Some(node_id) = descend(repo, arity, peak_left, peak_height, peak_id, left, height)? else {
        return Ok(None);
    };
    let Some(digest_id) = gitutil::find_entry(repo, node_id, "digest")? else {
        return Ok(None);
    };
    match gitutil::find_entry(repo, digest_id, &hex16(alg_id))? {
        Some(blob_id) => Ok(Some(gitutil::read_blob(repo, blob_id)?)),
        None => Ok(None),
    }
}

/// Decode `load_algorithm_metas`'s result from `tree_id`'s `epochs/`.
pub(crate) fn load_algorithm_metas(
    repo: &gix::Repository,
    tree_id: ObjectId,
) -> Result<polydigest::AlgorithmMetas, Error> {
    let Some(epochs_id) = gitutil::find_entry(repo, tree_id, "epochs")? else {
        return Ok(Vec::new());
    };
    let mut out = Vec::new();
    for e in gitutil::read_tree(repo, epochs_id)? {
        let alg = crate::layout::parse_hex16(&e.filename.to_string())
            .ok_or_else(|| corrupt(format!("epochs/ entry {} is not a hex(alg_id,16) name", e.filename)))?;
        let bytes = gitutil::read_blob(repo, e.oid)?;
        out.push((alg, crate::layout::decode_epochs(&bytes)?));
    }
    Ok(out)
}

/// Decode `load_checkpoint_roots`'s result from `tree_id`'s `roots/`.
pub(crate) fn load_checkpoint_roots(
    repo: &gix::Repository,
    tree_id: ObjectId,
) -> Result<Vec<(u64, Vec<u8>)>, Error> {
    let Some(roots_id) = gitutil::find_entry(repo, tree_id, "roots")? else {
        return Ok(Vec::new());
    };
    let mut out = Vec::new();
    for e in gitutil::read_tree(repo, roots_id)? {
        let alg = crate::layout::parse_hex16(&e.filename.to_string())
            .ok_or_else(|| corrupt(format!("roots/ entry {} is not a hex(alg_id,16) name", e.filename)))?;
        out.push((alg, gitutil::read_blob(repo, e.oid)?));
    }
    Ok(out)
}
