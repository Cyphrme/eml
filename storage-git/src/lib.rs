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

use std::path::Path;
use std::time::{Duration, Instant};

pub use error::GitStorageError;
use gix::ObjectId;
use gix::refs::transaction::{Change, LogChange, PreviousValue, RefEdit};
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
        let (observed_tip, count, has_leaves) = match local
            .try_find_reference(staging_ref.as_ref())
            .map_err(|e| GitStorageError::Git(e.to_string()))?
        {
            None => (None, 0, false),
            Some(mut r) => {
                let tree_id = r
                    .peel_to_id()
                    .map_err(|e| GitStorageError::Git(e.to_string()))?
                    .detach();
                let meta_id = gitutil::find_entry(&local, tree_id, "meta")?.ok_or_else(|| {
                    GitStorageError::Corruption("staging ref's tree has no meta".into())
                })?;
                let bytes = gitutil::read_blob(&local, meta_id)?;
                let (stored_arity, count) = layout::decode_meta(&bytes)?;
                if stored_arity != arity {
                    return Err(GitStorageError::InvalidArity(format!(
                        "instance arity {arity} disagrees with stored meta.arity {stored_arity}"
                    )));
                }
                let has_leaves = gitutil::find_entry(&local, tree_id, "leaves")?.is_some();
                (Some(tree_id), count, has_leaves)
            },
        };

        Ok(Self {
            repo,
            staging_ref,
            arity,
            observed_tip,
            count,
            has_leaves,
        })
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
    /// precondition (SG17-SG19). A genuine compare-mismatch
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
    /// retrying forever.
    fn cas(&self, repo: &gix::Repository, new_tree: ObjectId) -> Result<(), GitStorageError> {
        let expected = match self.observed_tip {
            Some(id) => PreviousValue::MustExistAndMatch(Target::Object(id)),
            None => PreviousValue::MustNotExist,
        };
        let start = Instant::now();
        let mut backoff = Duration::from_millis(5);
        loop {
            let edit = RefEdit {
                change: Change::Update {
                    log: LogChange::default(),
                    expected: expected.clone(),
                    new: Target::Object(new_tree),
                },
                name: self.staging_ref.clone(),
                deref: false,
            };
            match repo.edit_reference(edit) {
                Ok(_) => return Ok(()),
                Err(e) if is_genuine_cas_mismatch(&e) => {
                    let actual = repo
                        .try_find_reference(self.staging_ref.as_ref())
                        .ok()
                        .flatten()
                        .map(|r| r.target().id().to_owned().to_string());
                    return Err(GitStorageError::TipMoved {
                        expected: self.observed_tip.map(|id| id.to_string()),
                        actual,
                    });
                },
                Err(e) => {
                    let elapsed = start.elapsed();
                    if elapsed >= RETRY_BOUND {
                        return Err(GitStorageError::RefUpdateTransient(format!(
                            "ref update to {:?} failed without a compare-mismatch after retrying \
                             for {RETRY_BOUND:?}: {e}",
                            self.staging_ref
                        )));
                    }
                    std::thread::sleep(backoff.min(RETRY_BOUND - elapsed));
                    backoff = (backoff * 2).min(Duration::from_millis(100));
                },
            }
        }
    }
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

    async fn load_checkpoint_roots(&self) -> Result<Vec<(u64, Vec<u8>)>, Self::Error> {
        let Some(tree) = self.observed_tip else {
            return Ok(Vec::new());
        };
        let repo = self.thread_local();
        read::load_checkpoint_roots(&repo, tree)
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

    /// Load every active-at-this-tree algorithm's checkpoint root.
    ///
    /// # Errors
    ///
    /// Propagates a decode/corruption error.
    pub async fn load_checkpoint_roots(&self) -> Result<Vec<(u64, Vec<u8>)>, GitStorageError> {
        let repo = self.repo.to_thread_local();
        read::load_checkpoint_roots(&repo, self.tree)
    }
}
