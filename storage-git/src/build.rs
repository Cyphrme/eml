//! Checkpoint-tree assembly: turning a `write_batch` call's leaves/nodes/
//! algorithm-metas/checkpoint-roots into a new `C(n')` tree object (§2, §3,
//! SG17-SG19, SG22).
//!
//! The write algorithm never recomputes content it was not given and never
//! decomposes an already-sealed node further than treating it as an opaque
//! or materialized whole (SG18a "reusing unchanged children by object id
//! rather than rewriting them"): every coordinate in the new frontier is
//! either (a) an old peak untouched by this batch, reused by object id with
//! no I/O beyond the one-time read that seeded `old_index`, or (b) resolved
//! fresh from this batch's own data plus, for a node that already existed,
//! its previously-stored digest/leaf/children — the only cases the object
//! model needs to represent (§2.6).

use std::collections::HashMap;

use gix::ObjectId;
use gix::objs::tree::EntryKind;
use spine::frontier_for_size;

use crate::error::GitStorageError as Error;
use crate::gitutil::{self, entry};
use crate::layout::{self, hex2, hex16};

fn corrupt(msg: impl Into<String>) -> Error {
    Error::Corruption(msg.into())
}

/// This batch's freshly-provided node digests, keyed by coordinate: each
/// `(alg_id, hash)` pair a `write_batch` call's `nodes` argument carries for
/// that `(left, height)`.
type NodeMap<'a> = HashMap<(u64, u32), Vec<(u64, &'a [u8])>>;

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

#[derive(Clone, Copy)]
struct Resolved {
    id: ObjectId,
    materialized: bool,
}

/// Assemble and write the new checkpoint tree. Does not touch the staging
/// ref; the caller performs the compare-and-swap (SG18c) once this returns.
pub(crate) fn apply_write(
    repo: &gix::Repository,
    arity: u64,
    old_tree: Option<ObjectId>,
    old_count: u64,
    old_kind: u8,
    first_write: bool,
    input: &WriteInputs<'_>,
) -> Result<Applied, Error> {
    let new_count = input.log_meta.map_or(old_count, |(n, _)| n);
    let new_kind = input.log_meta.map_or(old_kind, |(_, k)| k);

    let leaf_map: HashMap<u64, &[u8]> = input.leaves.iter().map(|&(i, d)| (i, d)).collect();
    let mut node_map: NodeMap<'_> = HashMap::new();
    for &(alg, left, height, hash) in input.nodes {
        node_map.entry((left, height)).or_default().push((alg, hash));
    }

    let (epochs_tree, active_algs) = build_epochs(repo, old_tree, input.algorithm_metas, new_count)?;
    let roots_tree = build_roots(repo, old_tree, input.checkpoint_roots, &active_algs)?;
    let batch = BatchInputs { leaf_map: &leaf_map, node_map: &node_map, first_write };
    let peaks_tree = build_peaks(repo, arity, old_tree, old_count, new_count, &batch)?;

    let meta_blob = gitutil::write_blob(repo, &layout::encode_meta(arity, new_count, new_kind))?;
    let top = vec![
        entry(EntryKind::Blob, "meta", meta_blob),
        entry(EntryKind::Tree, "epochs", epochs_tree),
        entry(EntryKind::Tree, "roots", roots_tree),
        entry(EntryKind::Tree, "peaks", peaks_tree),
    ];
    let tree_id = gitutil::write_tree(repo, top)?;

    Ok(Applied {
        tree_id,
        count: new_count,
        kind_byte: new_kind,
    })
}

/// Build `epochs/` (§3.2, SG13) and return the set of algorithms active at
/// `new_count` (SG14 — only these get a `roots/` entry).
fn build_epochs(
    repo: &gix::Repository,
    old_tree: Option<ObjectId>,
    algorithm_metas: &[(u64, &[(u64, u64)])],
    new_count: u64,
) -> Result<(ObjectId, Vec<u64>), Error> {
    let mut alg_ids: Vec<u64> = match old_tree {
        Some(t) => list_epoch_algorithms(repo, t)?,
        None => Vec::new(),
    };
    for &(alg_id, _) in algorithm_metas {
        if !alg_ids.contains(&alg_id) {
            alg_ids.push(alg_id);
        }
    }

    let mut entries = Vec::new();
    let mut active = Vec::new();
    for alg_id in alg_ids {
        let history: Vec<(u64, u64)> =
            if let Some(&(_, epochs)) = algorithm_metas.iter().find(|&&(id, _)| id == alg_id) {
                epochs.to_vec()
            } else {
                let blob = read_named_blob(repo, old_tree, "epochs", alg_id)?.ok_or_else(|| {
                    corrupt(format!("algorithm {alg_id} registered but epochs/ blob missing"))
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
        entries.push(entry(EntryKind::Blob, hex16(alg_id), blob_id));
    }
    Ok((gitutil::write_tree(repo, entries)?, active))
}

/// Build `roots/` (§3.3, SG14): carry forward every still-active algorithm's
/// previous root, overlaid by this batch's fresh roots, dropped for anything
/// no longer active.
fn build_roots(
    repo: &gix::Repository,
    old_tree: Option<ObjectId>,
    checkpoint_roots: &[(u64, &[u8])],
    active_algs: &[u64],
) -> Result<ObjectId, Error> {
    let mut roots: HashMap<u64, Vec<u8>> = match old_tree {
        Some(t) => read_named_map(repo, t, "roots")?,
        None => HashMap::new(),
    };
    for &(alg_id, root) in checkpoint_roots {
        roots.insert(alg_id, root.to_vec());
    }
    roots.retain(|alg_id, _| active_algs.contains(alg_id));

    let mut entries = Vec::with_capacity(roots.len());
    for (alg_id, bytes) in &roots {
        entries.push(entry(EntryKind::Blob, hex16(*alg_id), gitutil::write_blob(repo, bytes)?));
    }
    gitutil::write_tree(repo, entries)
}

/// This batch's own raw inputs `build_peaks`/`resolve_node` need, bundled
/// only to stay under clippy's too-many-arguments threshold -- every field
/// is exactly one of `WriteInputs`' own borrows or the `first_write`
/// provenance flag [`resolve_node`]'s doc comment explains, never a
/// separate concept.
struct BatchInputs<'a> {
    leaf_map: &'a HashMap<u64, &'a [u8]>,
    node_map: &'a NodeMap<'a>,
    first_write: bool,
}

/// [`BatchInputs`] plus the coordinate index of `old_tree`'s own peaks --
/// everything [`resolve_node`]'s recursion needs, bundled for the same
/// too-many-arguments reason.
#[derive(Clone, Copy)]
struct ResolveCtx<'a> {
    leaf_map: &'a HashMap<u64, &'a [u8]>,
    node_map: &'a NodeMap<'a>,
    old_index: &'a HashMap<(u64, u32), Resolved>,
    first_write: bool,
}

/// Build `peaks/` (§2.1, SG1-SG2): the frontier at `new_count`, each peak
/// either reused unchanged from `old_tree` or freshly resolved.
fn build_peaks(
    repo: &gix::Repository,
    arity: u64,
    old_tree: Option<ObjectId>,
    old_count: u64,
    new_count: u64,
    batch: &BatchInputs<'_>,
) -> Result<ObjectId, Error> {
    let old_coords = frontier_for_size(old_count, arity);
    let old_index = index_old_peaks(repo, old_tree, &old_coords)?;
    let ctx = ResolveCtx {
        leaf_map: batch.leaf_map,
        node_map: batch.node_map,
        old_index: &old_index,
        first_write: batch.first_write,
    };

    let new_coords = frontier_for_size(new_count, arity);
    let mut by_height: HashMap<u32, Vec<u64>> = HashMap::new();
    for &(left, height) in &new_coords {
        by_height.entry(height).or_default().push(left);
    }

    let mut top = Vec::with_capacity(by_height.len());
    for (height, mut lefts) in by_height {
        lefts.sort_unstable();
        let mut group = Vec::with_capacity(lefts.len());
        for (q, left) in lefts.into_iter().enumerate() {
            let resolved = resolve_node(repo, arity, left, height, &ctx)?;
            group.push(entry(EntryKind::Tree, hex2(q as u64), resolved.id));
        }
        let group_tree = gitutil::write_tree(repo, group)?;
        top.push(entry(EntryKind::Tree, hex2(u64::from(height)), group_tree));
    }
    gitutil::write_tree(repo, top)
}

fn is_touched(
    left: u64,
    height: u32,
    leaf_map: &HashMap<u64, &[u8]>,
    node_map: &NodeMap<'_>,
) -> bool {
    node_map.contains_key(&(left, height)) || (height == 0 && leaf_map.contains_key(&left))
}

/// Whether a brand-new (never-before-existing) node at `(left, height)`
/// would end up materialized, without performing any I/O or writes — a pure
/// predicate over this batch's own data, so [`resolve_node`] can decide
/// whether to recurse into children before writing anything (never leaving
/// an orphaned child object behind for a node that turns out opaque, SG10).
fn would_materialize(
    k: u64,
    left: u64,
    height: u32,
    leaf_map: &HashMap<u64, &[u8]>,
    old_index: &HashMap<(u64, u32), Resolved>,
) -> bool {
    if let Some(r) = old_index.get(&(left, height)) {
        return r.materialized;
    }
    if height == 0 {
        leaf_map.contains_key(&left)
    } else {
        let span = k.pow(height - 1);
        (0..k).all(|c| would_materialize(k, left + c * span, height - 1, leaf_map, old_index))
    }
}

/// Resolve (reusing or freshly building) the node at `(left, height)`.
///
/// `first_write` is `true` only for this `GitStorage` instance's own first
/// successful `write_batch` (SG10/SG11): on that write, a *touched*
/// coordinate's prior occupant (if any) is not this instance's own -- it
/// belongs to whatever the staging ref happened to point at before this
/// instance ever wrote to it, which may be a superseded provenance
/// (`NaryMerkleLog::resume` reprovisioning a seal onto a ref an earlier,
/// now-obsolete instance already materialized). `existing` is therefore
/// forced to `None` for a touched coordinate on that one write, so
/// materialization and `digest/` are derived solely from what *this batch*
/// supplies, never carried forward from an unrelated occupant -- exactly
/// SG10's "digest/ only, no leaf, no children ... whatever object
/// previously existed at that coordinate". An *untouched* coordinate is
/// unaffected (the `is_touched` short-circuit above reuses it by object id
/// regardless, per SG18a); from this instance's second write onward,
/// `existing` again reflects this same instance's own prior writes, so
/// carrying it forward (e.g. `resume_algorithm` adding a digest to an
/// already-materialized leaf) is safe and required for `get_leaf` parity.
fn resolve_node(repo: &gix::Repository, k: u64, left: u64, height: u32, ctx: &ResolveCtx<'_>) -> Result<Resolved, Error> {
    let ResolveCtx { leaf_map, node_map, old_index, first_write } = *ctx;
    if !is_touched(left, height, leaf_map, node_map) {
        return old_index
            .get(&(left, height))
            .copied()
            .ok_or_else(|| corrupt(format!("no data for coordinate (left={left}, height={height})")));
    }

    let existing = if first_write { None } else { old_index.get(&(left, height)).copied() };

    let mut digest_map: HashMap<u64, Vec<u8>> = match existing {
        Some(r) => read_digest_map(repo, r.id)?,
        None => HashMap::new(),
    };
    if let Some(fresh) = node_map.get(&(left, height)) {
        for &(alg, hash) in fresh {
            digest_map.insert(alg, hash.to_vec());
        }
    }
    let mut digest_entries = Vec::with_capacity(digest_map.len());
    for (alg, bytes) in &digest_map {
        digest_entries.push(entry(EntryKind::Blob, hex16(*alg), gitutil::write_blob(repo, bytes)?));
    }
    let digest_tree = gitutil::write_tree(repo, digest_entries)?;
    let mut top = vec![entry(EntryKind::Tree, "digest", digest_tree)];

    let materialized = if height == 0 {
        let leaf_bytes: Option<Vec<u8>> = if let Some(&data) = leaf_map.get(&left) {
            Some(data.to_vec())
        } else if let Some(r) = existing {
            if r.materialized { read_leaf_blob(repo, r.id)? } else { None }
        } else {
            None
        };
        if let Some(bytes) = &leaf_bytes {
            top.push(entry(EntryKind::Blob, "leaf", gitutil::write_blob(repo, bytes)?));
        }
        leaf_bytes.is_some()
    } else if let Some(r) = existing {
        // Already existed: its shape (leaf/children presence) cannot change
        // through this trait (an opaque node has no backfill operation,
        // §2.6) -- carry the same children references forward unchanged.
        if r.materialized {
            for child in gitutil::read_tree(repo, r.id)? {
                if child.filename != "digest" {
                    top.push(entry(child.kind, child.filename, child.oid));
                }
            }
        }
        r.materialized
    } else {
        let span = k.pow(height - 1);
        let materialize =
            (0..k).all(|c| would_materialize(k, left + c * span, height - 1, leaf_map, old_index));
        if materialize {
            for c in 0..k {
                let child_left = left + c * span;
                let child = resolve_node(repo, k, child_left, height - 1, ctx)?;
                top.push(entry(EntryKind::Tree, hex2(c), child.id));
            }
        }
        materialize
    };

    let id = gitutil::write_tree(repo, top)?;
    Ok(Resolved { id, materialized })
}

/// Read every old peak's object id and materialization flag, keyed by
/// coordinate, so unchanged peaks can be reused with zero further I/O.
fn index_old_peaks(
    repo: &gix::Repository,
    old_tree: Option<ObjectId>,
    old_coords: &[(u64, u32)],
) -> Result<HashMap<(u64, u32), Resolved>, Error> {
    let Some(old_tree) = old_tree else {
        return Ok(HashMap::new());
    };
    if old_coords.is_empty() {
        return Ok(HashMap::new());
    }
    let peaks_id =
        gitutil::find_entry(repo, old_tree, "peaks")?.ok_or_else(|| corrupt("C(n) missing peaks/"))?;

    let mut by_height: HashMap<u32, Vec<u64>> = HashMap::new();
    for &(left, height) in old_coords {
        by_height.entry(height).or_default().push(left);
    }

    let mut out = HashMap::new();
    for (height, mut lefts) in by_height {
        lefts.sort_unstable();
        let group_id = gitutil::find_entry(repo, peaks_id, &hex2(u64::from(height)))?
            .ok_or_else(|| corrupt(format!("missing peaks/{}", hex2(u64::from(height)))))?;
        for (q, left) in lefts.into_iter().enumerate() {
            let node_id = gitutil::find_entry(repo, group_id, &hex2(q as u64))?.ok_or_else(|| {
                corrupt(format!("missing peaks/{}/{}", hex2(u64::from(height)), hex2(q as u64)))
            })?;
            let materialized = node_is_materialized(repo, node_id, height)?;
            out.insert((left, height), Resolved { id: node_id, materialized });
        }
    }
    Ok(out)
}

fn node_is_materialized(repo: &gix::Repository, node_id: ObjectId, height: u32) -> Result<bool, Error> {
    let entries = gitutil::read_tree(repo, node_id)?;
    if height == 0 {
        Ok(entries.iter().any(|e| e.filename == "leaf"))
    } else {
        Ok(entries.iter().any(|e| e.filename != "digest"))
    }
}

fn read_digest_map(repo: &gix::Repository, node_id: ObjectId) -> Result<HashMap<u64, Vec<u8>>, Error> {
    let Some(digest_id) = gitutil::find_entry(repo, node_id, "digest")? else {
        return Ok(HashMap::new());
    };
    let mut map = HashMap::new();
    for e in gitutil::read_tree(repo, digest_id)? {
        let alg = layout::parse_hex16(&e.filename.to_string())
            .ok_or_else(|| corrupt(format!("digest/ entry {} is not a hex(alg_id,16) name", e.filename)))?;
        map.insert(alg, gitutil::read_blob(repo, e.oid)?);
    }
    Ok(map)
}

fn read_leaf_blob(repo: &gix::Repository, node_id: ObjectId) -> Result<Option<Vec<u8>>, Error> {
    match gitutil::find_entry(repo, node_id, "leaf")? {
        Some(id) => Ok(Some(gitutil::read_blob(repo, id)?)),
        None => Ok(None),
    }
}

fn list_epoch_algorithms(repo: &gix::Repository, tree: ObjectId) -> Result<Vec<u64>, Error> {
    let Some(epochs_id) = gitutil::find_entry(repo, tree, "epochs")? else {
        return Ok(Vec::new());
    };
    gitutil::read_tree(repo, epochs_id)?
        .into_iter()
        .map(|e| {
            layout::parse_hex16(&e.filename.to_string())
                .ok_or_else(|| corrupt(format!("epochs/ entry {} is not a hex(alg_id,16) name", e.filename)))
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

fn read_named_map(repo: &gix::Repository, tree: ObjectId, section: &str) -> Result<HashMap<u64, Vec<u8>>, Error> {
    let Some(section_id) = gitutil::find_entry(repo, tree, section)? else {
        return Ok(HashMap::new());
    };
    let mut map = HashMap::new();
    for e in gitutil::read_tree(repo, section_id)? {
        let alg = layout::parse_hex16(&e.filename.to_string())
            .ok_or_else(|| corrupt(format!("{section}/ entry {} is not a hex(alg_id,16) name", e.filename)))?;
        map.insert(alg, gitutil::read_blob(repo, e.oid)?);
    }
    Ok(map)
}
