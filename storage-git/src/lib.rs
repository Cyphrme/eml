//! Git-backed storage backend for the EML append-only library.
//!
//! Implements `polydigest`'s [`Storage`] trait over a git object database
//! reached through `gix`, per `docs/specs/storage-git.md`. Git is mere
//! storage here: nothing in this crate trusts a git object id as a security
//! boundary, and no hash algorithm is ever named (SG26) -- every digest this
//! layer persists is caller-supplied bytes, and it queries
//! `Repository::object_hash()` rather than assuming SHA-1 or SHA-256 (SG27).
//!
//! # The key-derived layout
//!
//! Every node and leaf lives at a git tree path derived **only** from its
//! own key -- `nodes/hex16(alg_id)/hex2(height)/<trimmed(left)>` for a node,
//! `leaves/<trimmed(index)>` for a leaf, where `trimmed` is the
//! `byte1-be-trim` scheme (`src/layout.rs::trimmed_key_segments`; design
//! rationale in `docs/specs/storage-git.md` §2.1). A write adds exactly the
//! keys it is given: no peak-and-children hierarchy, no decomposition of a
//! taller coordinate into its parts, no materialized-versus-opaque
//! distinction, and nothing wired or carried forward by decision. This
//! replaces an earlier peak-wired layout (`peaks/hex(height,2)/hex(q,2)/…`)
//! that had to reconstruct every frontier coordinate's children from
//! scratch on each write and, in doing so, could silently drop a
//! descendant that stopped being a frontier peak
//! (`completeness_property.rs`'s dropped-node finding); the key-derived
//! layout has no such reconstruction step to get wrong, since every
//! coordinate a write is ever handed keeps its own permanent, independent
//! path for the life of the log.
//!
//! # Departures from the spec's literal text
//!
//! 1. **Arity is a constructor parameter, not trait-carried.** `Storage` never passes `k`; it is
//!    not part of the key-derived layout at all beyond `meta.arity` (§3.1). [`GitStorage::new`]
//!    takes `arity` explicitly and persists it in `meta` (SG12); reopening against a tree whose
//!    stored arity disagrees is rejected as [`GitStorageError::InvalidArity`].
//! 2. **`apply`'s `AppendLeaf`/`AppendSubtree` ops require in-order positions.** A
//!    [`polydigest::WriteOp::AppendLeaf`]/[`polydigest::WriteOp::AppendSubtree`]'s `at` is accepted
//!    only at `at == append_count()`, matching the same append-only assumption `MemoryStorage`
//!    already makes via its own explicit precondition check in `apply`. Nothing about the
//!    key-derived layout itself requires in-order writes -- every key is independent -- this
//!    constraint exists only to keep `len()`/`meta.count` (which the layout does still track, §3.1)
//!    a faithful count of contiguous leaves.
//!
//! # The tip-tree model
//!
//! This layer keeps the **complete** checkpoint tree behind its staging ref: every leaf and
//! sealed node ever written, by key, forever. The staging ref always points
//! **directly at a tree object** (never a commit), and [`GitStorage::tip_tree`] hands back the
//! tree this instance last wrote or observed. This layer never creates a commit and never
//! renders or reconstructs a tree for a size other than its current one: a past size is read by
//! wrapping an earlier tip tree in a commit one layer up (the checkpoint library this crate is
//! deliberately ignorant of), and by `eml` reading over the nodes the complete tip tree already
//! contains.

mod build;
mod error;
mod gitutil;
mod layout;
mod read;

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

pub use error::GitStorageError;
use gix::ObjectId;
use gix::refs::transaction::{Change, LogChange, PreviousValue, RefEdit, RefLog};
use gix::refs::{FullName, Target};
use polydigest::{AlgorithmMetas, LogKind, Storage, WriteOp};

/// The bound `cas()`'s internal retry loop honors for a definitely-non-
/// mismatch ref-update failure (SG19a): give up and return
/// [`GitStorageError::RefUpdateTransient`] once this much wall-clock time
/// has elapsed since the first attempt, rather than retrying forever. A
/// genuine compare-mismatch is never retried internally regardless of this
/// bound -- it returns [`GitStorageError::TipMoved`] on the first attempt.
const RETRY_BOUND: Duration = Duration::from_secs(2);

/// A checkpoint's log metadata (head's ruling, 2026-09-17, requirement E):
/// the append count and the derived kind, so the checkpoint layer above
/// this crate never decodes `meta`'s raw bytes -- or reasons about kind
/// derivation -- itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LogMetadata {
    /// The total number of log-level appends committed at this checkpoint.
    pub count: u64,
    /// The derived kind (never stored -- see [`Storage::len`]'s doc comment
    /// for the derivation this mirrors). `LogKind::Flat` at `count == 0`,
    /// where either kind is equally valid.
    pub kind: LogKind,
}

/// A `polydigest::Storage` backend over a git object database.
///
/// Not `Clone`, mirroring `storage-fjall`'s `FjallStorage`: single-writer
/// ownership is what SG17-SG19's "the race is only ever against another
/// process" narrowing relies on.
pub struct GitStorage {
    repo: gix::ThreadSafeRepository,
    staging_ref: FullName,
    /// Where `staging_ref`'s loose file lives, and the directory its path is
    /// relative to: the paths SG33's ref sync covers when recovery resets it.
    ref_file: PathBuf,
    ref_base: PathBuf,
    /// `<staging>.ckpt/`, the prefix of this store's checkpoint refs (SG32).
    ckpt_prefix: String,
    arity: u64,
    /// The tree id this instance last observed at `staging_ref`, or `None`
    /// for a fresh instance whose ref has never been created (genesis; the
    /// next write's compare-and-swap uses `MustNotExist`). Populated once,
    /// in [`Self::new`], from a lookup of `staging_ref` alone -- never from
    /// scanning the backing repository's object database or any other ref.
    /// `append_count` (below) reports `0` exactly when this is `None`, so a
    /// repository that hosts several logs side by side, each under its own
    /// staging ref (e.g. a fork: sealing one ref and resuming into a
    /// brand-new ref in the same repository), reports freshness correctly
    /// per ref -- one ref's committed log is never visible through another.
    observed_tip: Option<ObjectId>,
    count: u64,
    /// Whether the observed tree has any `leaves/` entry at all -- the
    /// signal [`Self::metadata`] derives `LogKind` from (see
    /// [`derive_log_metadata`]), maintained alongside `count` rather than
    /// re-walked from the tree on every call.
    has_leaves: bool,
}

impl GitStorage {
    /// Open a `storage-git` instance over `repo`'s `staging_ref` (SG17),
    /// creating the ref lazily on the first write rather than here.
    ///
    /// If a valid checkpoint exists (SG32) this also recovers (SG34): staging
    /// that is intact is kept (and checkpointed if ahead), anything else is
    /// reset to the newest checkpoint. Recovery reads only the subtrees that
    /// differ between staging and that checkpoint, so it costs O(entries of
    /// the trees changed since the last checkpoint), never a walk of the store.
    ///
    /// # Errors
    ///
    /// Returns [`GitStorageError::InvalidArity`] if `arity` is outside
    /// `spine::ARITY_RANGE`, or disagrees with an existing checkpoint's
    /// stored `meta.arity`; [`GitStorageError::InvalidRef`] if
    /// `staging_ref` is not a valid git reference name;
    /// [`GitStorageError::Corruption`] if an existing staging ref does not
    /// point at a well-formed checkpoint tree.
    pub fn new(
        repo: gix::ThreadSafeRepository,
        staging_ref: impl AsRef<str>,
        arity: u64,
    ) -> Result<Self, GitStorageError> {
        if !spine::ARITY_RANGE.contains(&arity) {
            return Err(GitStorageError::InvalidArity(format!(
                "arity {arity} outside {:?}",
                spine::ARITY_RANGE
            )));
        }
        let staging_ref: FullName = staging_ref
            .as_ref()
            .try_into()
            .map_err(|_| GitStorageError::InvalidRef(staging_ref.as_ref().to_string()))?;

        let local = repo.to_thread_local();
        let (ref_file, ref_base) = loose_ref_path(&local, &staging_ref)?;
        let ckpt_prefix = ckpt_prefix(&staging_ref)?;

        // Newest valid checkpoint, if any (SG32); a valid one with the wrong
        // arity is the caller's error, as for staging.
        let ckpts = list_ckpts(&local, &ckpt_prefix, arity)?;
        let newest = ckpts.iter().rev().find_map(|c| c.snap);

        // What staging held when read, for the reset's compare-and-swap.
        enum Prior {
            Absent,
            Value(ObjectId),
            Torn,
        }
        let mut needs_checkpoint = false;
        let mut reset: Option<Prior> = None;
        let staging = match (read_snap(&local, &staging_ref, arity), newest) {
            (Ok(staging), None) => staging,
            (Err(e @ GitStorageError::Git(_)), None) => {
                return Err(GitStorageError::NoDurableState(format!(
                    "staging ref {:?} is unreadable and no checkpoint exists: {e}",
                    staging_ref.as_bstr()
                )));
            },
            (Err(e), None) => return Err(e),
            (Err(e @ GitStorageError::InvalidArity(_)), Some(_)) => return Err(e),
            (Ok(Some(s)), Some(c)) if s.tree == c.tree => Some(s),
            (Ok(Some(s)), Some(c)) => {
                // Append counts do not order states (`AddAlgorithm` changes
                // the tree and not the count), and staging was made durable
                // before the checkpoint was written, so a staging that
                // differs from the checkpoint is a later state: keep it if
                // everything it adds over the checkpoint reads (a power loss
                // can leave the ref durable ahead of an object).
                if gitutil::changed_objects(&local, s.tree, Some(c.tree), &mut Vec::new()).is_ok() {
                    needs_checkpoint = true;
                    Some(s)
                } else {
                    reset = Some(Prior::Value(s.tree));
                    Some(c)
                }
            },
            (Ok(None), Some(c)) => {
                reset = Some(Prior::Absent);
                Some(c)
            },
            (Err(_), Some(c)) => {
                reset = Some(Prior::Torn);
                Some(c)
            },
        };

        let mut this = Self {
            repo,
            staging_ref,
            ref_file,
            ref_base,
            ckpt_prefix,
            arity,
            observed_tip: staging.map(|s| s.tree),
            count: staging.map_or(0, |s| s.count),
            has_leaves: staging.is_some_and(|s| s.has_leaves),
        };
        if let Some(prior) = reset {
            // Staging is torn, empty, or names a hole: point it back at the
            // checkpoint, which was synced before it was recorded. The write
            // is a compare-and-swap against what was read. A torn ref has no
            // value to compare against, so it is re-read and must still be
            // torn.
            let tree = this.observed_tip.expect("a reset always has a checkpoint");
            let (expected, seen) = match prior {
                Prior::Absent => (PreviousValue::MustNotExist, None),
                Prior::Value(t) => (PreviousValue::MustExistAndMatch(Target::Object(t)), Some(t)),
                Prior::Torn => {
                    if let Ok(Some(now)) = read_snap(&local, &this.staging_ref, arity) {
                        return Err(GitStorageError::TipMoved {
                            expected: None,
                            actual: Some(now.tree.to_string()),
                        });
                    }
                    (PreviousValue::Any, None)
                },
            };
            update_ref(&local, &this.staging_ref, expected, tree, seen)?;
            let packed = local.common_dir().join("packed-refs");
            gitutil::sync_ref_any_form(&this.ref_file, &this.ref_base, &packed)?;
        } else if needs_checkpoint {
            this.checkpoint()?;
        }
        Ok(this)
    }

    /// Open a `storage-git` instance against the repository at `path`
    /// (opened with `gix::ThreadSafeRepository::open`).
    ///
    /// # Errors
    ///
    /// Propagates a `gix` open failure, or anything [`Self::new`] returns.
    pub fn open(
        path: &Path,
        staging_ref: impl AsRef<str>,
        arity: u64,
    ) -> Result<Self, GitStorageError> {
        let repo = gix::ThreadSafeRepository::open(path)
            .map_err(|e| GitStorageError::Git(e.to_string()))?;
        Self::new(repo, staging_ref, arity)
    }

    /// The tree this instance last wrote or observed, or `None` for a fresh
    /// instance whose ref has never been written (genesis).
    ///
    /// This is a pure read of [`Self::new`]'s last-observed value (or the
    /// value a subsequent write left behind) -- never a reconstruction, and
    /// never a re-read of the staging ref's own live value (a concurrent
    /// writer may have moved it since; this instance would report that only
    /// on its own next write's compare-and-swap, as [`GitStorageError::TipMoved`]).
    /// The checkpoint layer above this crate commits this tree to anchor it;
    /// this crate itself never renders or reconstructs a tree for any other
    /// size (see "The tip-tree model" above).
    #[must_use]
    pub fn tip_tree(&self) -> Option<ObjectId> {
        self.observed_tip
    }

    /// This instance's current log metadata: append count and derived kind
    /// (head's ruling, 2026-09-17, requirement E), so a caller (e.g. the
    /// checkpoint layer) never needs to decode `meta`'s raw bytes or derive
    /// kind itself.
    #[must_use]
    pub fn metadata(&self) -> LogMetadata {
        derive_log_metadata(self.count, self.has_leaves)
    }

    /// A read-only view over an arbitrary checkpoint tree (§4.4, SG21),
    /// independent of this instance's own staging ref and current size.
    ///
    /// # Errors
    ///
    /// Returns [`GitStorageError::Corruption`] if `tree` does not decode as
    /// a well-formed checkpoint tree.
    pub fn open_at(&self, tree: ObjectId) -> Result<GitReadOnlyView, GitStorageError> {
        let repo = self.repo.to_thread_local();
        let meta_id = gitutil::find_entry(&repo, tree, "meta")?
            .ok_or_else(|| GitStorageError::Corruption("tree has no meta".into()))?;
        let bytes = gitutil::read_blob(&repo, meta_id)?;
        let (_arity, count) = layout::decode_meta(&bytes)?;
        let has_leaves = gitutil::find_entry(&repo, tree, "leaves")?.is_some();
        Ok(GitReadOnlyView {
            repo: self.repo.clone(),
            tree,
            size: count,
            has_leaves,
        })
    }

    /// Make everything applied so far durable, and return the append count
    /// that is now.
    ///
    /// `apply` syncs nothing (SG31); this syncs every object reachable from
    /// the staging tip that the newest checkpoint cannot reach, with the
    /// directories naming them; then the staging ref itself; and only then
    /// creates the next checkpoint ref and syncs it. So a surviving
    /// checkpoint implies a durable staging at that value or a later one, and
    /// no checkpoint is ever durable ahead of what it names. Every ref
    /// is made durable whether git holds it loose or packed (SG33).
    ///
    /// Checkpoint refs are `<staging>.ckpt/<generation>`, the generation a
    /// 20-digit zero-padded `u64` one greater than the largest present; this
    /// creates the new ref only if absent, then drops all but the newest
    /// valid earlier one, leaving at most two. Append counts do not order
    /// states (`AddAlgorithm` changes the tree and not the count);
    /// generations do. A staging ref with a path component ending in `.ckpt`
    /// is refused at open, so stores never share a checkpoint ref.
    ///
    /// Cost: a tree walk limited to the subtrees that differ from the newest
    /// checkpoint, so proportional to the work applied since it (intermediate
    /// trees of batches the tip no longer reaches are never read or synced),
    /// plus a constant number of ref syncs. With no checkpoint yet the first
    /// one walks the whole tree. A store with nothing applied returns `0`.
    ///
    /// # Errors
    ///
    /// [`GitStorageError::TipMoved`] if the staging ref no longer holds this
    /// instance's tip, or the generation to create was taken by another
    /// process; [`GitStorageError::Sync`] if an object, directory or ref
    /// cannot be synced; [`GitStorageError::Corruption`] if an object the tip
    /// names is missing.
    pub fn checkpoint(&mut self) -> Result<u64, GitStorageError> {
        let Some(tip) = self.observed_tip else {
            return Ok(0);
        };
        let repo = self.thread_local();
        match read_snap(&repo, &self.staging_ref, self.arity) {
            Ok(Some(s)) if s.tree == tip => {},
            other => {
                return Err(GitStorageError::TipMoved {
                    expected: Some(tip.to_string()),
                    actual: other.ok().flatten().map(|s| s.tree.to_string()),
                });
            },
        }
        let ckpts = list_ckpts(&repo, &self.ckpt_prefix, self.arity)?;
        let newest = ckpts.iter().rev().find(|c| c.snap.is_some());
        let newest_snap = newest.and_then(|c| c.snap);
        if newest_snap.is_some_and(|n| n.tree == tip) {
            return Ok(self.count);
        }
        let mut delta = Vec::new();
        gitutil::changed_objects(&repo, tip, newest_snap.map(|n| n.tree), &mut delta)?;
        let mut unsynced = gitutil::Unsynced::default();
        for id in &delta {
            unsynced.object(&repo, *id);
        }
        unsynced.sync(&repo)?;
        let packed = repo.common_dir().join("packed-refs");
        gitutil::sync_ref_any_form(&self.ref_file, &self.ref_base, &packed)?;

        let next = ckpts.last().map_or(1, |c| c.generation + 1);
        let name = ckpt_name(&self.ckpt_prefix, next)?;
        update_ref(&repo, &name, PreviousValue::MustNotExist, tip, None)?;
        let (file, base) = loose_ref_path(&repo, &name)?;
        gitutil::sync_ref_any_form(&file, &base, &packed)?;

        // Best effort: a stale extra checkpoint is harmless (recovery takes
        // the newest) and the next checkpoint drops it again.
        let keep = newest.map(|c| c.generation);
        for c in ckpts.iter().filter(|c| Some(c.generation) != keep) {
            let _ = repo.edit_reference(RefEdit {
                change: Change::Delete {
                    expected: PreviousValue::MustExistAndMatch(Target::Object(c.target)),
                    log: RefLog::AndReference,
                },
                name: c.name.clone(),
                deref: false,
            });
        }
        Ok(self.count)
    }

    fn thread_local(&self) -> gix::Repository {
        self.repo.to_thread_local()
    }

    /// The leaf-specific count [`Storage::len`] must report: `count` for a
    /// flat log, `0` for a subtree-kind log regardless of its append count
    /// (see that method's own doc comment) -- a log is monotonically one or
    /// the other once it has ever appended, so `has_leaves` alone decides
    /// it.
    fn leaf_len(&self) -> u64 {
        if self.has_leaves { self.count } else { 0 }
    }

    /// Move the staging ref to `new_tree` under its compare-and-swap
    /// precondition (SG17-SG19); see [`update_ref`].
    fn cas(&self, repo: &gix::Repository, new_tree: ObjectId) -> Result<(), GitStorageError> {
        let expected = match self.observed_tip {
            Some(id) => PreviousValue::MustExistAndMatch(Target::Object(id)),
            None => PreviousValue::MustNotExist,
        };
        update_ref(
            repo,
            &self.staging_ref,
            expected,
            new_tree,
            self.observed_tip,
        )
    }
}

/// What a ref's tree says about the log it holds.
#[derive(Clone, Copy)]
struct Snap {
    tree: ObjectId,
    count: u64,
    has_leaves: bool,
}

/// One existing checkpoint ref.
struct CkptRef {
    generation: u64,
    name: FullName,
    target: ObjectId,
    /// What its tree says, or `None` if the ref or its tree is torn.
    snap: Option<Snap>,
}

/// `<staging>.ckpt/`, the prefix of `staging`'s checkpoint refs. Two stores'
/// checkpoint refs coincide only if their staging refs do. A staging ref with
/// a path component ending in `.ckpt` is refused, since it could itself be
/// (or sit under) some store's checkpoint ref.
fn ckpt_prefix(staging: &FullName) -> Result<String, GitStorageError> {
    use gix::bstr::ByteSlice as _;
    let staging = staging.as_bstr().to_str_lossy();
    if staging.split('/').any(|c| c.ends_with(".ckpt")) {
        return Err(GitStorageError::InvalidRef(format!(
            "{staging}: a path component ending in `.ckpt` is reserved for checkpoint refs"
        )));
    }
    Ok(format!("{staging}.ckpt/"))
}

fn ckpt_name(prefix: &str, generation: u64) -> Result<FullName, GitStorageError> {
    let full = format!("{prefix}{generation:020}");
    full.as_str()
        .try_into()
        .map_err(|_| GitStorageError::InvalidRef(full.clone()))
}

/// Every checkpoint ref under `prefix`, loose or packed, by generation. A
/// ref whose name is not a generation is not ours and is skipped.
fn list_ckpts(
    repo: &gix::Repository,
    prefix: &str,
    arity: u64,
) -> Result<Vec<CkptRef>, GitStorageError> {
    use gix::bstr::ByteSlice as _;
    let git = |e: &dyn std::fmt::Display| GitStorageError::Git(e.to_string());
    let mut out = Vec::new();
    let platform = repo.references().map_err(|e| git(&e))?;
    for r in platform.prefixed(prefix).map_err(|e| git(&e))? {
        let Ok(r) = r else { continue };
        let Some(target) = r.try_id().map(gix::Id::detach) else {
            continue;
        };
        let name = r.name().to_owned();
        let Some(generation) = name
            .as_bstr()
            .to_str_lossy()
            .strip_prefix(prefix)
            .filter(|g| g.len() == 20)
            .and_then(|g| g.parse::<u64>().ok())
        else {
            continue;
        };
        let snap = match read_snap(repo, &name, arity) {
            Ok(snap) => snap,
            Err(e @ GitStorageError::InvalidArity(_)) => return Err(e),
            Err(_) => None,
        };
        out.push(CkptRef {
            generation,
            name,
            target,
            snap,
        });
    }
    out.sort_by_key(|c| c.generation);
    Ok(out)
}

/// Read the tree `name` targets as a checkpoint tree: `None` if the ref is
/// absent, an error if it is torn or its tree is malformed.
fn read_snap(
    repo: &gix::Repository,
    name: &FullName,
    arity: u64,
) -> Result<Option<Snap>, GitStorageError> {
    let Some(mut r) = repo
        .try_find_reference(name.as_ref())
        .map_err(|e| GitStorageError::Git(e.to_string()))?
    else {
        return Ok(None);
    };
    let tree = r
        .peel_to_id()
        .map_err(|e| GitStorageError::Git(e.to_string()))?
        .detach();
    let meta_id = gitutil::find_entry(repo, tree, "meta")?
        .ok_or_else(|| GitStorageError::Corruption("ref's tree has no meta".into()))?;
    let bytes = gitutil::read_blob(repo, meta_id)?;
    let (stored_arity, count) = layout::decode_meta(&bytes)?;
    if stored_arity != arity {
        return Err(GitStorageError::InvalidArity(format!(
            "instance arity {arity} disagrees with stored meta.arity {stored_arity}"
        )));
    }
    let has_leaves = gitutil::find_entry(repo, tree, "leaves")?.is_some();
    Ok(Some(Snap {
        tree,
        count,
        has_leaves,
    }))
}

/// Move `name` to `new_tree` under `expected` (SG17-SG19). A genuine
/// compare-mismatch
/// (`ReferenceOutOfDate`/`MustNotExist`/`MustExist` -- the only
/// `gix_ref` transaction variants that ever reached the point of
/// comparing a value) returns [`GitStorageError::TipMoved`] immediately,
/// never retried: deciding what to write in light of someone else's
/// real change is the caller's job, not this layer's. Every other
/// failure shape (a lock a concurrent `git gc`/`pack-refs` briefly
/// holds, an I/O error, a packed-refs preparation failure) never
/// touched the ref's value at all, so it is safe to retry the identical
/// edit internally -- bounded by [`RETRY_BOUND`], past which this gives
/// up and returns [`GitStorageError::RefUpdateTransient`] rather than
/// retrying forever. `observed` is what the caller expected, for the
/// mismatch report.
fn update_ref(
    repo: &gix::Repository,
    name: &FullName,
    expected: PreviousValue,
    new_tree: ObjectId,
    observed: Option<ObjectId>,
) -> Result<(), GitStorageError> {
    let start = Instant::now();
    let mut backoff = Duration::from_millis(5);
    loop {
        let edit = RefEdit {
            change: Change::Update {
                log: LogChange::default(),
                expected: expected.clone(),
                new: Target::Object(new_tree),
            },
            name: name.clone(),
            deref: false,
        };
        match repo.edit_reference(edit) {
            Ok(_) => return Ok(()),
            Err(e) if is_genuine_cas_mismatch(&e) => {
                let actual = repo
                    .try_find_reference(name.as_ref())
                    .ok()
                    .flatten()
                    .map(|r| r.target().id().to_owned().to_string());
                return Err(GitStorageError::TipMoved {
                    expected: observed.map(|id| id.to_string()),
                    actual,
                });
            },
            Err(e) => {
                let elapsed = start.elapsed();
                if elapsed >= RETRY_BOUND {
                    return Err(GitStorageError::RefUpdateTransient(format!(
                        "ref update to {:?} failed without a compare-mismatch after retrying for \
                         {RETRY_BOUND:?}: {e}",
                        name
                    )));
                }
                std::thread::sleep(backoff.min(RETRY_BOUND - elapsed));
                backoff = (backoff * 2).min(Duration::from_millis(100));
            },
        }
    }
}

/// The loose file `gix-ref` writes `name` to, and the directory that path is
/// relative to. Mirrors `gix-ref` 0.67.1's `file::Store::reference_path`
/// (`store/file/find.rs`), which is crate-private. A name in another
/// worktree's namespace (`main-worktree/`, `worktrees/<id>/`) is refused:
/// this layer does not resolve where such a file lives, so it could not
/// sync it (SG31).
fn loose_ref_path(
    repo: &gix::Repository,
    name: &FullName,
) -> Result<(PathBuf, PathBuf), GitStorageError> {
    use gix::bstr::ByteSlice as _;
    use gix::refs::Category;
    let base = match name.as_ref().category() {
        None
        | Some(Category::Tag | Category::LocalBranch | Category::RemoteBranch | Category::Note) => {
            repo.common_dir()
        },
        Some(
            Category::PseudoRef
            | Category::Bisect
            | Category::Rewritten
            | Category::WorktreePrivate,
        ) => repo.git_dir(),
        Some(
            Category::MainRef
            | Category::MainPseudoRef
            | Category::LinkedRef { .. }
            | Category::LinkedPseudoRef { .. },
        ) => {
            return Err(GitStorageError::InvalidRef(format!(
                "{name:?} names another worktree's ref, which storage-git cannot sync (SG31)"
            )));
        },
    };
    let mut relative = repo
        .namespace()
        .map(|ns| ns.as_bstr().to_owned())
        .unwrap_or_default();
    relative.extend_from_slice(name.as_bstr());
    let file = base.join(gix::path::from_bstr(relative.as_bstr()));
    Ok((file, base.to_path_buf()))
}

/// SG19a: true only for the `gix_ref` transaction-preparation errors that
/// mean "the ref's current value did not match what this write expected" --
/// the only condition [`GitStorageError::TipMoved`] should ever report.
/// Every other `edit_reference` failure shape (lock contention, I/O, a
/// packed-refs preparation failure, or any `gix_ref::file::transaction::
/// commit::Error` variant, which has no mismatch case at all) means the
/// transaction never reached, or never completed, an actual value
/// comparison.
fn is_genuine_cas_mismatch(e: &gix::reference::edit::Error) -> bool {
    matches!(
        e,
        gix::reference::edit::Error::FileTransactionPrepare(
            gix::refs::file::transaction::prepare::Error::ReferenceOutOfDate { .. }
                | gix::refs::file::transaction::prepare::Error::MustNotExist { .. }
                | gix::refs::file::transaction::prepare::Error::MustExist { .. }
        )
    )
}

impl Storage for GitStorage {
    type Error = GitStorageError;

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        let Some(tree) = self.observed_tip else {
            return Err(GitStorageError::NotFound(format!(
                "leaf index {index} (empty store)"
            )));
        };
        let repo = self.thread_local();
        read::get_leaf(&repo, tree, self.leaf_len(), index)
    }

    async fn len(&self) -> Result<u64, Self::Error> {
        Ok(self.leaf_len())
    }

    async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Option<Vec<u8>>, Self::Error> {
        let Some(tree) = self.observed_tip else {
            return Ok(None);
        };
        let repo = self.thread_local();
        read::get_node(&repo, tree, alg_id, left, height)
    }

    async fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, Self::Error> {
        let Some(tree) = self.observed_tip else {
            return Ok(Vec::new());
        };
        let repo = self.thread_local();
        read::load_algorithm_metas(&repo, tree)
    }

    async fn append_count(&self) -> Result<u64, Self::Error> {
        Ok(self.count)
    }

    async fn apply(&mut self, ops: &[WriteOp<'_>]) -> Result<(), Self::Error> {
        let repo = self.thread_local();
        let old = build::OldState {
            tree: self.observed_tip,
            count: self.count,
            has_leaves: self.has_leaves,
        };
        let applied = build::apply(&repo, self.arity, old, ops)?;
        self.cas(&repo, applied.tree_id)?;
        self.observed_tip = Some(applied.tree_id);
        self.count = applied.count;
        self.has_leaves = applied.has_leaves;
        Ok(())
    }
}

/// Derive a checkpoint's [`LogMetadata`] from exactly the `(count,
/// has_leaves)` pair [`GitStorage::metadata`] and
/// [`GitReadOnlyView::metadata`] both carry, so the two never duplicate the
/// derivation: `LogKind::Flat` at `count == 0` (either kind is equally
/// valid there) or whenever any leaf has ever been written; `LogKind::Subtree`
/// otherwise (a nonzero count with no leaves -- a resumed or
/// subtree-appended-from-genesis log).
fn derive_log_metadata(count: u64, has_leaves: bool) -> LogMetadata {
    let kind = if count == 0 || has_leaves {
        LogKind::Flat
    } else {
        LogKind::Subtree
    };
    LogMetadata { count, kind }
}

/// A read-only view over one checkpoint tree, returned by
/// [`GitStorage::open_at`] (§4.4, SG21). Exposes exactly the trait's read
/// methods that make sense against a frozen historical tree; carries no
/// mutation and no dependency on the instance that produced it.
pub struct GitReadOnlyView {
    repo: gix::ThreadSafeRepository,
    tree: ObjectId,
    size: u64,
    has_leaves: bool,
}

impl GitReadOnlyView {
    /// The checkpoint tree this view reads from.
    #[must_use]
    pub fn tree(&self) -> ObjectId {
        self.tree
    }

    /// This view's log metadata: append count and derived kind (head's
    /// ruling, 2026-09-17, requirement E) -- see [`GitStorage::metadata`].
    #[must_use]
    pub fn metadata(&self) -> LogMetadata {
        derive_log_metadata(self.size, self.has_leaves)
    }

    /// Read item `index`'s raw leaf payload.
    ///
    /// # Errors
    ///
    /// Returns [`GitStorageError::NotFound`] if `index` is out of range or
    /// was never materialized.
    pub async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, GitStorageError> {
        let repo = self.repo.to_thread_local();
        read::get_leaf(&repo, self.tree, self.size, index)
    }

    /// Read a sealed node digest at `(alg_id, left, height)`.
    ///
    /// # Errors
    ///
    /// Propagates a decode/corruption error.
    pub async fn get_node(
        &self,
        alg_id: u64,
        left: u64,
        height: u32,
    ) -> Result<Option<Vec<u8>>, GitStorageError> {
        let repo = self.repo.to_thread_local();
        read::get_node(&repo, self.tree, alg_id, left, height)
    }

    /// Load every registered algorithm's epoch history as projected onto
    /// this view's tree.
    ///
    /// # Errors
    ///
    /// Propagates a decode/corruption error.
    pub async fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, GitStorageError> {
        let repo = self.repo.to_thread_local();
        read::load_algorithm_metas(&repo, self.tree)
    }
}

#[cfg(test)]
mod tests {
    //! SG31's coverage: what `checkpoint` syncs, read through the recording seam
    //! in `gitutil`'s `sync_if_present`. A power loss itself is not simulated.

    use std::collections::HashSet;
    use std::path::PathBuf;

    use polydigest::{NodeWrite, Storage, WriteOp};

    use super::GitStorage;
    use crate::gitutil::SYNCED;

    /// After a run of applies and one checkpoint, every loose object file
    /// the tip reaches and every directory naming one was synced, the
    /// checkpoint ref's file and each directory from it up to the git
    /// directory were synced, and every object sync preceded the ref's.
    #[test]
    fn checkpoint_syncs_every_object_and_the_ref() {
        let dir = tempfile::tempdir().unwrap();
        let repo = gix::ThreadSafeRepository::init_opts(
            dir.path(),
            gix::create::Kind::Bare,
            gix::create::Options::default(),
            Default::default(),
        )
        .unwrap();
        let mut storage = GitStorage::new(repo, "refs/eml/storage/sync/staging", 2).unwrap();
        let git_dir = dir.path().to_path_buf();
        let ref_file = git_dir.join("refs/eml/storage/sync/staging.ckpt/00000000000000000001");
        let staging_file = git_dir.join("refs/eml/storage/sync/staging");
        let objects = git_dir.join("objects");

        SYNCED.with(|s| s.borrow_mut().clear());
        for i in 0..8u64 {
            let data = i.to_be_bytes();
            let hash = [u8::try_from(i).unwrap(); 32];
            let nodes = [NodeWrite {
                alg_id: 1,
                left: i,
                height: 0,
                hash: &hash,
            }];
            smol::block_on(storage.apply(&[WriteOp::AppendLeaf {
                at: i,
                data: &data,
                nodes: &nodes,
            }]))
            .unwrap();
        }
        assert!(
            SYNCED.with(|s| s.borrow().is_empty()),
            "apply must sync nothing"
        );
        assert_eq!(storage.checkpoint().unwrap(), 8);
        let this = SYNCED.with(|s| s.borrow().clone());
        let staging_at = this.iter().position(|p| *p == staging_file).unwrap();
        let ref_at = this.iter().position(|p| *p == ref_file).unwrap();
        assert!(
            staging_at < ref_at,
            "the checkpoint ref was synced before the staging ref: {this:?}"
        );
        assert!(
            this[..staging_at].iter().all(|p| p.starts_with(&objects)),
            "something other than an object synced before the refs: {this:?}"
        );
        assert!(
            this[staging_at..].iter().all(|p| !p.starts_with(&objects)),
            "an object synced after the refs: {this:?}"
        );

        let synced: HashSet<PathBuf> = this.into_iter().collect();
        let mut expected = vec![
            objects.clone(),
            ref_file.clone(),
            staging_file.clone(),
            git_dir.join("refs/eml/storage/sync"),
            git_dir.join("refs/eml/storage/sync/staging.ckpt"),
            git_dir.join("refs/eml/storage"),
            git_dir.join("refs/eml"),
            git_dir.join("refs"),
            git_dir.clone(),
        ];
        // Only what the tip reaches is owed durability: the trees of
        // earlier applies are unreachable and never read or synced.
        let listing = std::process::Command::new("git")
            .arg("--git-dir")
            .arg(&git_dir)
            .args(["rev-list", "--objects"])
            .arg(storage.tip_tree().unwrap().to_string())
            .output()
            .unwrap();
        assert!(listing.status.success());
        for line in String::from_utf8(listing.stdout).unwrap().lines() {
            let hex = line.split(' ').next().unwrap();
            let fanout = objects.join(&hex[..2]);
            expected.push(fanout.join(&hex[2..]));
            expected.push(fanout);
        }
        let missing: Vec<_> = expected.iter().filter(|p| !synced.contains(*p)).collect();
        assert!(missing.is_empty(), "never synced: {missing:?}");
    }

    /// A compare-and-swap that does not match is refused as `TipMoved` and
    /// leaves the ref as it was: the primitive every checkpoint and reset
    /// write goes through.
    #[test]
    fn update_ref_refuses_a_mismatch_and_leaves_the_ref() {
        use gix::refs::Target;
        use gix::refs::transaction::PreviousValue;

        let dir = tempfile::tempdir().unwrap();
        let repo = gix::ThreadSafeRepository::init_opts(
            dir.path(),
            gix::create::Kind::Bare,
            gix::create::Options::default(),
            Default::default(),
        )
        .unwrap()
        .to_thread_local();
        let (a, b) = (
            repo.empty_tree().id,
            repo.write_blob(b"x").unwrap().detach(),
        );
        let name: gix::refs::FullName = "refs/eml/storage/u/staging".try_into().unwrap();

        super::update_ref(&repo, &name, PreviousValue::MustNotExist, a, None).unwrap();
        for expected in [
            PreviousValue::MustNotExist,
            PreviousValue::MustExistAndMatch(Target::Object(b)),
        ] {
            let err = super::update_ref(&repo, &name, expected, b, None).unwrap_err();
            assert!(err.is_tip_moved(), "{err}");
            let held = repo.find_reference(name.as_ref()).unwrap().id().detach();
            assert_eq!(held, a, "a refused update moved the ref");
        }
    }
}
