//! Key-derived reads (§2, §2.2) against an arbitrary checkpoint tree: shared
//! by the live staged-tree reads (`Storage::get_leaf`/`get_node`) and
//! [`crate::GitStorage::open_at`]'s read-only view.
//!
//! Pure path resolution, no decomposition and no fallback: a key not
//! present at its derived path was simply never written, so `get_node`
//! answers `Ok(None)` and `get_leaf` answers `Err(NotFound)` honestly
//! rather than reconstructing anything.

use gix::ObjectId;

use crate::error::GitStorageError as Error;
use crate::gitutil;
use crate::layout::{
    TOP_LEVEL_EPOCHS, TOP_LEVEL_LEAVES, TOP_LEVEL_NODES, hex2, hex16, trimmed_key_segments,
};

/// Read item `index`'s raw leaf payload out of the checkpoint tree at
/// `tree_id` (currently `size` items).
pub(crate) fn get_leaf(
    repo: &gix::Repository,
    tree_id: ObjectId,
    size: u64,
    index: u64,
) -> Result<Vec<u8>, Error> {
    if index >= size {
        return Err(Error::NotFound(format!("leaf index {index} (size {size})")));
    }
    let Some(l) = gitutil::find_entry(repo, tree_id, TOP_LEVEL_LEAVES)? else {
        return Err(Error::NotFound(format!("leaf {index} (no leaves written)")));
    };
    match gitutil::resolve_at_path(repo, l, &trimmed_key_segments(index))? {
        Some(id) => gitutil::read_blob(repo, id),
        None => Err(Error::NotFound(format!(
            "leaf {index} was never given (no entry at its key path)"
        ))),
    }
}

/// Read a sealed node digest at `(alg_id, left, height)` out of the
/// checkpoint tree at `tree_id`.
pub(crate) fn get_node(
    repo: &gix::Repository,
    tree_id: ObjectId,
    alg_id: u64,
    left: u64,
    height: u32,
) -> Result<Option<Vec<u8>>, Error> {
    let Some(n) = gitutil::find_entry(repo, tree_id, TOP_LEVEL_NODES)? else {
        return Ok(None);
    };
    let mut segments = vec![hex16(alg_id), hex2(u64::from(height))];
    segments.extend(trimmed_key_segments(left));
    match gitutil::resolve_at_path(repo, n, &segments)? {
        Some(id) => Ok(Some(gitutil::read_blob(repo, id)?)),
        None => Ok(None),
    }
}

/// Decode `load_algorithm_metas`'s result from `tree_id`'s `epochs/`.
pub(crate) fn load_algorithm_metas(
    repo: &gix::Repository,
    tree_id: ObjectId,
) -> Result<polydigest::AlgorithmMetas, Error> {
    let Some(e) = gitutil::find_entry(repo, tree_id, TOP_LEVEL_EPOCHS)? else {
        return Ok(Vec::new());
    };
    let mut out = Vec::new();
    for entry in gitutil::read_tree(repo, e)? {
        let alg = crate::layout::parse_hex16(&entry.filename.to_string()).ok_or_else(|| {
            Error::Corruption(format!(
                "epochs/ entry {} is not a hex(alg_id,16) name",
                entry.filename
            ))
        })?;
        let bytes = gitutil::read_blob(repo, entry.oid)?;
        out.push((alg, crate::layout::decode_epochs(&bytes)?));
    }
    Ok(out)
}
