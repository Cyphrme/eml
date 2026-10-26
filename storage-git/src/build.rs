//! Checkpoint-tree assembly: turning a [`polydigest::WriteOp`] batch into a
//! new `C(n')` tree object (§2, §3), per the key-derived layout
//! (`docs/specs/storage-git.md` §2.1): a node or leaf is placed at a path
//! derived *only* from its key, and nothing else is ever recomputed from it
//! -- no peak/child wiring, no decomposition, no opacity bookkeeping. A
//! write adds exactly the keys it is given, with nothing wired or carried
//! forward by decision.
//!
//! `meta`/`epochs` are the one exception: small, non-key-addressed
//! metadata this function rewrites on every call, whether this batch's own
//! ops touched a given algorithm or not. For an algorithm this batch never
//! names, that rewrite is byte-identical to what was already stored --
//! `layout::epochs_at` returns the epoch history verbatim whenever the log
//! has only moved forward, which it always has by the time `apply` runs --
//! so the entry is not mutated in the sense of changing its content, only
//! refreshed in the sense of being written again with a new object id and a
//! fresh mtime (SG22). That refresh has no effect on an entry already
//! reachable from the previous tip (it was never a prune candidate), so the
//! only entries this refresh does real work for are the ones a newly
//! *registered* algorithm needs written for the first time; the redundant
//! rewrite of every other still-active algorithm's entry is a bounded,
//! small O(algorithms) cost per `apply` call, not a correctness
//! requirement.
//!
//! The whole batch is applied through one [`gix::object::tree::Editor`]
//! session (every ancestor a call's ops touch more than once is written to
//! the object database exactly once, on the single final `write()`, SG18).
//! The detached, unvalidated raw editor is used deliberately for that final
//! write -- the higher-level wrapper's `write()` re-validates every entry
//! of every changed tree on every call (an `objects.has()` existence probe
//! per entry, scaling with bucket width), which the spike measured as
//! slower wall-clock than a per-key write despite writing fewer objects;
//! every entry upserted here was already produced by this crate's own
//! [`crate::gitutil::write_blob`] a few lines above, so that validation is
//! redundant for this crate's own writes.

use std::collections::{HashMap, HashSet};

use gix::ObjectId;
use gix::objs::WriteTo as _;
use gix::objs::tree::EntryKind;
use polydigest::WriteOp;

use crate::error::GitStorageError as Error;
use crate::gitutil;
use crate::layout::{
    self, TOP_LEVEL_EPOCHS, TOP_LEVEL_LEAVES, TOP_LEVEL_META, TOP_LEVEL_NODES, hex2, hex16,
    trimmed_key_segments,
};

/// A top-level `roots` section this layer never writes, but may have
/// inherited from a tree a pre-removal version of this crate committed
/// (SG1: "no other top-level entry MUST ever exist -- in particular, no
/// `roots` entry ever exists, at any `n`"). `gix::object::tree::Editor`
/// carries every entry a batch's own ops never touch forward from the
/// previous tree unchanged, so a section already at rest would otherwise
/// survive indefinitely unless every `apply` call removes it explicitly,
/// whether or not this batch's own ops ever mentioned it.
const LEGACY_TOP_LEVEL_ROOTS: &str = "roots";

fn invalid(msg: impl Into<String>) -> Error {
    Error::InvalidOperation(msg.into())
}

fn corrupt(msg: impl Into<String>) -> Error {
    Error::Corruption(msg.into())
}

fn git_err(e: impl std::fmt::Display) -> Error {
    Error::Git(e.to_string())
}

/// The result of assembling and writing a new `C(n')`.
pub(crate) struct Applied {
    pub tree_id: ObjectId,
    pub count: u64,
    /// Whether `C(n')` has any `leaves/` entry at all -- the signal
    /// [`crate::GitStorage::metadata`]/[`crate::GitReadOnlyView::metadata`]
    /// derive `LogKind` from, carried forward here so neither has to
    /// re-walk the tree to answer it.
    pub has_leaves: bool,
}

/// The instance's committed state as of its last observed write: every
/// field [`apply`] reads once and projects forward (unless this write
/// replaces it).
#[derive(Clone, Copy)]
pub(crate) struct OldState {
    pub tree: Option<ObjectId>,
    pub count: u64,
    pub has_leaves: bool,
}

fn node_path(alg_id: u64, height: u32, left: u64) -> String {
    let mut segs = vec![
        TOP_LEVEL_NODES.to_string(),
        hex16(alg_id),
        hex2(u64::from(height)),
    ];
    segs.extend(trimmed_key_segments(left));
    segs.join("/")
}

fn leaf_path(index: u64) -> String {
    let mut segs = vec![TOP_LEVEL_LEAVES.to_string()];
    segs.extend(trimmed_key_segments(index));
    segs.join("/")
}

fn epochs_path(alg_id: u64) -> String {
    format!("{TOP_LEVEL_EPOCHS}/{}", hex16(alg_id))
}

/// Whether `alg_id` already has an `epochs/` entry in `tree` -- the
/// "already registered" oracle [`apply`]'s precondition checks read.
fn epochs_entry_exists(
    repo: &gix::Repository,
    tree: Option<ObjectId>,
    alg_id: u64,
) -> Result<bool, Error> {
    let Some(tree) = tree else {
        return Ok(false);
    };
    let Some(epochs_tree) = gitutil::find_entry(repo, tree, TOP_LEVEL_EPOCHS)? else {
        return Ok(false);
    };
    Ok(gitutil::find_entry(repo, epochs_tree, &hex16(alg_id))?.is_some())
}

/// Every algorithm id `tree` has an `epochs/` entry for -- the base set
/// [`apply`]'s final refresh pass projects forward, whether this batch's
/// ops touched them or not.
fn known_algorithm_ids(repo: &gix::Repository, tree: Option<ObjectId>) -> Result<Vec<u64>, Error> {
    let Some(tree) = tree else {
        return Ok(Vec::new());
    };
    let Some(epochs_tree) = gitutil::find_entry(repo, tree, TOP_LEVEL_EPOCHS)? else {
        return Ok(Vec::new());
    };
    gitutil::read_tree(repo, epochs_tree)?
        .into_iter()
        .map(|e| {
            layout::parse_hex16(&e.filename.to_string()).ok_or_else(|| {
                corrupt(format!(
                    "epochs/ entry {} is not a hex(alg_id,16) name",
                    e.filename
                ))
            })
        })
        .collect()
}

/// Read and decode one algorithm's currently-stored `epochs/hex16(alg_id)`
/// blob from `tree` -- the "carry forward unchanged" source for an
/// algorithm this batch's ops never mention.
fn read_stored_epochs(
    repo: &gix::Repository,
    tree: Option<ObjectId>,
    alg_id: u64,
) -> Result<Vec<(u64, u64)>, Error> {
    let Some(tree) = tree else {
        return Err(corrupt(format!(
            "algorithm {alg_id} has no epochs/ entry to carry forward (no prior tree)"
        )));
    };
    let epochs_tree = gitutil::find_entry(repo, tree, TOP_LEVEL_EPOCHS)?
        .ok_or_else(|| corrupt("tree has no epochs/ section"))?;
    let blob_id = gitutil::find_entry(repo, epochs_tree, &hex16(alg_id))?.ok_or_else(|| {
        corrupt(format!(
            "algorithm {alg_id} has no epochs/{} entry to carry forward",
            hex16(alg_id)
        ))
    })?;
    layout::decode_epochs(&gitutil::read_blob(repo, blob_id)?)
}

/// Assemble and write the new checkpoint tree for one atomic batch of
/// [`polydigest::WriteOp`]s, and sync every object it wrote to disk
/// (SG31). Does not touch the staging ref; the caller performs the
/// compare-and-swap once this returns.
pub(crate) fn apply(
    repo: &gix::Repository,
    arity: u64,
    old: OldState,
    ops: &[WriteOp<'_>],
) -> Result<Applied, Error> {
    let root_tree = match old.tree {
        Some(id) => repo.find_tree(id).map_err(git_err)?,
        None => repo.empty_tree(),
    };
    let mut editor = root_tree.edit().map_err(git_err)?;
    let mut unsynced = gitutil::Unsynced::default();

    // Make SG1's "no roots entry ever exists" true by construction rather
    // than by assumption about what the previous tree happened to carry: a
    // no-op on a tree that has none, so no fresh log's tree id moves.
    editor.remove(LEGACY_TOP_LEVEL_ROOTS).map_err(git_err)?;

    let mut count = old.count;
    let mut has_leaves = old.has_leaves;

    // Per-algorithm effects this batch's ops carry, collected as the ops
    // are walked and applied to `epochs` in one final pass below --
    // deferred because that pass must know every OTHER currently-known
    // algorithm too (to refresh their unchanged entries, SG22), which is
    // only knowable once this batch's own registrations are complete.
    let mut registered_this_batch: HashSet<u64> = HashSet::new();
    let mut epoch_overrides: HashMap<u64, Vec<(u64, u64)>> = HashMap::new();

    let known = |registered_this_batch: &HashSet<u64>, alg_id: u64| -> Result<bool, Error> {
        Ok(registered_this_batch.contains(&alg_id) || epochs_entry_exists(repo, old.tree, alg_id)?)
    };

    for op in ops {
        match op {
            WriteOp::AppendLeaf { at, data, nodes } => {
                if *at != count {
                    return Err(invalid(format!(
                        "AppendLeaf at position {at}, expected the current count {count}"
                    )));
                }
                let blob = gitutil::write_blob(repo, &mut unsynced, data)?;
                editor
                    .upsert(leaf_path(*at).as_str(), EntryKind::Blob, blob)
                    .map_err(git_err)?;
                for n in *nodes {
                    let node_blob = gitutil::write_blob(repo, &mut unsynced, n.hash)?;
                    editor
                        .upsert(
                            node_path(n.alg_id, n.height, n.left).as_str(),
                            EntryKind::Blob,
                            node_blob,
                        )
                        .map_err(git_err)?;
                }
                count += 1;
                has_leaves = true;
            },
            WriteOp::AppendSubtree { at, nodes } => {
                if *at != count {
                    return Err(invalid(format!(
                        "AppendSubtree at position {at}, expected the current count {count}"
                    )));
                }
                for n in *nodes {
                    let node_blob = gitutil::write_blob(repo, &mut unsynced, n.hash)?;
                    editor
                        .upsert(
                            node_path(n.alg_id, n.height, n.left).as_str(),
                            EntryKind::Blob,
                            node_blob,
                        )
                        .map_err(git_err)?;
                }
                count += 1;
            },
            WriteOp::AddAlgorithm { alg_id, epochs } => {
                if known(&registered_this_batch, *alg_id)? {
                    return Err(invalid(format!("algorithm {alg_id} is already registered")));
                }
                epoch_overrides.insert(*alg_id, epochs.to_vec());
                registered_this_batch.insert(*alg_id);
            },
            WriteOp::RemoveAlgorithm { alg_id, epochs } => {
                if !known(&registered_this_batch, *alg_id)? {
                    return Err(invalid(format!("algorithm {alg_id} is not registered")));
                }
                epoch_overrides.insert(*alg_id, epochs.to_vec());
            },
            WriteOp::ResumeAlgorithm {
                alg_id,
                epochs,
                nodes,
            } => {
                if !known(&registered_this_batch, *alg_id)? {
                    return Err(invalid(format!("algorithm {alg_id} is not registered")));
                }
                epoch_overrides.insert(*alg_id, epochs.to_vec());
                for n in *nodes {
                    let node_blob = gitutil::write_blob(repo, &mut unsynced, n.hash)?;
                    editor
                        .upsert(
                            node_path(n.alg_id, n.height, n.left).as_str(),
                            EntryKind::Blob,
                            node_blob,
                        )
                        .map_err(git_err)?;
                }
            },
            WriteOp::SeedFrontier { size, algorithms } => {
                if count != 0 || !registered_this_batch.is_empty() {
                    return Err(invalid(
                        "SeedFrontier requires a fresh store: append_count must be 0 and no \
                         algorithm registered by an earlier op in this batch"
                            .to_string(),
                    ));
                }
                if !known_algorithm_ids(repo, old.tree)?.is_empty() {
                    return Err(invalid(
                        "SeedFrontier requires a fresh store: no algorithm may already be \
                         registered"
                            .to_string(),
                    ));
                }
                count = *size;
                for seed in *algorithms {
                    if known(&registered_this_batch, seed.alg_id)? {
                        return Err(invalid(format!(
                            "algorithm {} is already registered",
                            seed.alg_id
                        )));
                    }
                    epoch_overrides.insert(seed.alg_id, seed.epochs.to_vec());
                    for n in seed.nodes {
                        let node_blob = gitutil::write_blob(repo, &mut unsynced, n.hash)?;
                        editor
                            .upsert(
                                node_path(n.alg_id, n.height, n.left).as_str(),
                                EntryKind::Blob,
                                node_blob,
                            )
                            .map_err(git_err)?;
                    }
                    registered_this_batch.insert(seed.alg_id);
                }
            },
        }
    }

    // Project epochs/ forward for every currently-known algorithm -- old
    // ones this batch never mentioned, plus any it just registered --
    // applying this batch's own overrides where it has one. This refreshes
    // an otherwise-unchanged blob's object on every write (SG22), exactly as
    // every leaf/node write already does.
    let mut all_ids = known_algorithm_ids(repo, old.tree)?;
    for &id in &registered_this_batch {
        if !all_ids.contains(&id) {
            all_ids.push(id);
        }
    }

    for alg_id in all_ids {
        let epochs = match epoch_overrides.get(&alg_id) {
            Some(e) => e.clone(),
            None => read_stored_epochs(repo, old.tree, alg_id)?,
        };
        let projected = layout::epochs_at(&epochs, count).ok_or_else(|| {
            corrupt(format!(
                "algorithm {alg_id}'s epoch history does not cover size {count}"
            ))
        })?;
        let epochs_blob =
            gitutil::write_blob(repo, &mut unsynced, &layout::encode_epochs(&projected))?;
        editor
            .upsert(epochs_path(alg_id).as_str(), EntryKind::Blob, epochs_blob)
            .map_err(git_err)?;
    }

    let meta_blob = gitutil::write_blob(repo, &mut unsynced, &layout::encode_meta(arity, count))?;
    editor
        .upsert(TOP_LEVEL_META, EntryKind::Blob, meta_blob)
        .map_err(git_err)?;

    let mut raw = editor.detach();
    let tree_id: ObjectId = raw.write(|tree| {
        let mut buf = Vec::new();
        tree.write_to(&mut buf).map_err(git_err)?;
        gitutil::write_object(repo, &mut unsynced, gix::objs::Kind::Tree, &buf)
    })?;
    unsynced.sync()?;

    Ok(Applied {
        tree_id,
        count,
        has_leaves,
    })
}
