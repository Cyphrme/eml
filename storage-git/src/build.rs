//! Checkpoint-tree assembly: turning a `write_batch` call's leaves/nodes/
//! algorithm-metas/checkpoint-roots into a new `C(n')` tree object (§2, §3),
//! per THE DESIGN (`spike-report.md` and its prototype `storage-git-keyed/`):
//! a node or leaf is placed at a path derived *only* from its key, and
//! nothing else is ever recomputed from it -- no peak/child wiring, no
//! decomposition, no opacity bookkeeping. A write adds exactly the keys it
//! is given, with nothing wired or carried forward by decision.
//!
//! `meta`/`e`/`r` are the one exception: small, non-key-addressed metadata
//! that is genuinely mutated (not just appended to) on each write, so it is
//! projected forward from the prior tree the same way every write, touched
//! or not.
//!
//! The whole batch is applied through one `gix_object::tree::Editor` session
//! (one call to [`apply_write`] issues exactly one batched raw tree edit,
//! never one independent read-modify-write chain per key): every ancestor
//! touched by more than one key in this batch is written to the object
//! database exactly once, on the single final `write()` call. The detached,
//! unvalidated raw editor is used deliberately -- the higher-level wrapper's
//! `write()` re-validates every entry of every changed tree on every call
//! (an `objects.has()` existence probe per entry, scaling with bucket
//! width), which the spike measured as slower wall-clock than a per-key
//! write despite writing fewer objects; every entry upserted here was
//! already produced by this crate's own [`crate::gitutil::write_blob`] a few
//! lines above, so that validation is redundant for this crate's own writes.

use std::collections::HashMap;

use gix::ObjectId;
use gix::objs::WriteTo as _;
use gix::objs::tree::EntryKind;

use crate::error::GitStorageError as Error;
use crate::gitutil;
use crate::layout::{self, hex2, hex16, trimmed_key_segments};

fn corrupt(msg: impl Into<String>) -> Error {
    Error::Corruption(msg.into())
}

fn git_err(e: impl std::fmt::Display) -> Error {
    Error::Git(e.to_string())
}

/// The inputs a `Storage::write_batch` call carries, borrowed for the
/// duration of one [`apply_write`] call.
pub(crate) struct WriteInputs<'a> {
    pub leaves: &'a [(u64, &'a [u8])],
    pub nodes: &'a [(u64, u64, u32, &'a [u8])],
    pub algorithm_metas: &'a [(u64, &'a [(u64, u64)])],
    pub log_meta: Option<(u64, u8)>,
    pub checkpoint_roots: &'a [(u64, &'a [u8])],
}

/// The result of assembling and writing a new `C(n')`.
pub(crate) struct Applied {
    pub tree_id: ObjectId,
    pub count: u64,
    pub kind_byte: u8,
}

/// The instance's committed state as of its last observed write, bundled
/// only to stay under clippy's too-many-arguments threshold -- every field
/// is a distinct fact [`apply_write`] reads once and projects forward
/// (unless this write replaces it), never a single concept split apart.
#[derive(Clone, Copy)]
pub(crate) struct OldState {
    pub tree: Option<ObjectId>,
    pub count: u64,
    pub kind: u8,
}

fn node_path(alg_id: u64, height: u32, left: u64) -> String {
    let mut segs = vec![hex16(alg_id), hex2(u64::from(height))];
    segs.extend(trimmed_key_segments(left));
    format!("n/{}", segs.join("/"))
}

fn leaf_path(index: u64) -> String {
    format!("l/{}", trimmed_key_segments(index).join("/"))
}

/// Assemble and write the new checkpoint tree. Does not touch the staging
/// ref; the caller performs the compare-and-swap once this returns.
pub(crate) fn apply_write(
    repo: &gix::Repository,
    arity: u64,
    old: OldState,
    input: &WriteInputs<'_>,
) -> Result<Applied, Error> {
    let root_tree = match old.tree {
        Some(id) => repo.find_tree(id).map_err(git_err)?,
        None => repo.empty_tree(),
    };
    let mut editor = root_tree.edit().map_err(git_err)?;

    for &(index, data) in input.leaves {
        let blob = gitutil::write_blob(repo, data)?;
        editor
            .upsert(leaf_path(index).as_str(), EntryKind::Blob, blob)
            .map_err(git_err)?;
    }

    for &(alg_id, left, height, hash) in input.nodes {
        let blob = gitutil::write_blob(repo, hash)?;
        editor
            .upsert(
                node_path(alg_id, height, left).as_str(),
                EntryKind::Blob,
                blob,
            )
            .map_err(git_err)?;
    }

    let new_count = input.log_meta.map_or(old.count, |(n, _)| n);
    let requested_kind = input.log_meta.map_or(old.kind, |(_, k)| k);
    // SG9: canonicalize away the size-0 kind ambiguity. At count==0 a fresh
    // log and an empty-seal resume are observationally identical through
    // every polydigest accessor, so encoding the requested kind there would
    // make two provenance-different-but-content-identical logs produce
    // different tree ids for no observable benefit.
    let new_kind = if new_count == 0 { 0 } else { requested_kind };

    apply_epochs_and_roots(repo, old.tree, &mut editor, input, new_count)?;

    let meta_blob = gitutil::write_blob(repo, &layout::encode_meta(arity, new_count, new_kind))?;
    editor
        .upsert("meta", EntryKind::Blob, meta_blob)
        .map_err(git_err)?;

    let mut raw = editor.detach();
    let tree_id: ObjectId = raw.write(|tree| {
        let mut buf = Vec::new();
        tree.write_to(&mut buf).map_err(git_err)?;
        gitutil::write_object(repo, gix::objs::Kind::Tree, &buf)
    })?;

    Ok(Applied {
        tree_id,
        count: new_count,
        kind_byte: new_kind,
    })
}

/// Project `e/` (epoch history) and `r/` (checkpoint roots) forward,
/// applying this batch's own updates. An algorithm active at `new_count`
/// keeps (or gains) an `r/` entry; every other previously-known algorithm's
/// `r/` entry, if any, is removed.
fn apply_epochs_and_roots(
    repo: &gix::Repository,
    old_tree: Option<ObjectId>,
    editor: &mut gix::object::tree::Editor<'_>,
    input: &WriteInputs<'_>,
    new_count: u64,
) -> Result<(), Error> {
    let mut alg_ids: Vec<u64> = match old_tree {
        Some(t) => list_hex16_children(repo, t, "e")?,
        None => Vec::new(),
    };
    for &(alg_id, _) in input.algorithm_metas {
        if !alg_ids.contains(&alg_id) {
            alg_ids.push(alg_id);
        }
    }

    let mut old_roots: HashMap<u64, Vec<u8>> = match old_tree {
        Some(t) => read_named_map(repo, t, "r")?,
        None => HashMap::new(),
    };
    for &(alg_id, root) in input.checkpoint_roots {
        old_roots.insert(alg_id, root.to_vec());
    }

    let mut active = Vec::new();
    for &alg_id in &alg_ids {
        let history: Vec<(u64, u64)> = if let Some(&(_, epochs)) =
            input.algorithm_metas.iter().find(|&&(id, _)| id == alg_id)
        {
            epochs.to_vec()
        } else {
            let blob = read_named_blob(repo, old_tree, "e", alg_id)?.ok_or_else(|| {
                corrupt(format!("algorithm {alg_id} registered but e/ blob missing"))
            })?;
            layout::decode_epochs(&blob)?
        };
        let Some(projected) = layout::epochs_at(&history, new_count) else {
            continue;
        };
        if layout::is_active_at(&projected) {
            active.push(alg_id);
        }
        let blob_id = gitutil::write_blob(repo, &layout::encode_epochs(&projected))?;
        editor
            .upsert(
                format!("e/{}", hex16(alg_id)).as_str(),
                EntryKind::Blob,
                blob_id,
            )
            .map_err(git_err)?;
    }

    // SG9's note: at new_count == 0 there is no committed append for either
    // construction path to bind a root to, so a caller-supplied root value
    // here is exactly as observationally meaningless as the kind byte is --
    // `NaryMerkleLog::new`'s eager `add_algorithm` never supplies one at
    // genesis, while `NaryMerkleLog::resume` from an empty seal always does
    // (the empty view's own computed root), and the two provenances must
    // still commit the identical `C(0)`. Suppressing every `r/` entry at
    // count 0, regardless of what this batch was handed, closes that gap
    // the same way the kind canonicalization above does.
    for &alg_id in &alg_ids {
        let keep = new_count > 0 && active.contains(&alg_id);
        if keep {
            if let Some(bytes) = old_roots.get(&alg_id) {
                let blob_id = gitutil::write_blob(repo, bytes)?;
                editor
                    .upsert(
                        format!("r/{}", hex16(alg_id)).as_str(),
                        EntryKind::Blob,
                        blob_id,
                    )
                    .map_err(git_err)?;
                continue;
            }
        }
        editor
            .remove(format!("r/{}", hex16(alg_id)).as_str())
            .map_err(git_err)?;
    }

    Ok(())
}

fn list_hex16_children(
    repo: &gix::Repository,
    tree: ObjectId,
    section: &str,
) -> Result<Vec<u64>, Error> {
    let Some(section_id) = gitutil::find_entry(repo, tree, section)? else {
        return Ok(Vec::new());
    };
    gitutil::read_tree(repo, section_id)?
        .into_iter()
        .map(|e| {
            layout::parse_hex16(&e.filename.to_string()).ok_or_else(|| {
                corrupt(format!(
                    "{section}/ entry {} is not a hex(alg_id,16) name",
                    e.filename
                ))
            })
        })
        .collect()
}

fn read_named_blob(
    repo: &gix::Repository,
    tree: Option<ObjectId>,
    section: &str,
    alg_id: u64,
) -> Result<Option<Vec<u8>>, Error> {
    let Some(tree) = tree else { return Ok(None) };
    let Some(section_id) = gitutil::find_entry(repo, tree, section)? else {
        return Ok(None);
    };
    match gitutil::find_entry(repo, section_id, &hex16(alg_id))? {
        Some(id) => Ok(Some(gitutil::read_blob(repo, id)?)),
        None => Ok(None),
    }
}

fn read_named_map(
    repo: &gix::Repository,
    tree: ObjectId,
    section: &str,
) -> Result<HashMap<u64, Vec<u8>>, Error> {
    let Some(section_id) = gitutil::find_entry(repo, tree, section)? else {
        return Ok(HashMap::new());
    };
    let mut map = HashMap::new();
    for e in gitutil::read_tree(repo, section_id)? {
        let alg = layout::parse_hex16(&e.filename.to_string()).ok_or_else(|| {
            corrupt(format!(
                "{section}/ entry {} is not a hex(alg_id,16) name",
                e.filename
            ))
        })?;
        map.insert(alg, gitutil::read_blob(repo, e.oid)?);
    }
    Ok(map)
}
