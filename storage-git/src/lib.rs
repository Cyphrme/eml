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
//! THE DESIGN, ratified by two spikes (`spike-report.md` and its prototype
//! crate `storage-git-keyed/`, both under `.worktrees/spike-key-layout/`):
//! every node and leaf lives at a git tree path derived **only** from its
//! own key -- `n/hex16(alg_id)/hex2(height)/<trimmed(left)>` for a node,
//! `l/<trimmed(index)>` for a leaf, where `trimmed` is the `byte1-be-trim`
//! scheme (`src/layout.rs::trimmed_key_segments`). A write adds exactly the
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
//! 2. **Standalone `store_leaf`/`store_node` require in-order leaf indices.** A standalone
//!    `store_leaf(index, _)` is accepted only at `index == len()`, matching the same append-only
//!    assumption `MemoryStorage` already makes via its own `debug_assert_eq!`. Nothing about the
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
use polydigest::{AlgorithmMetas, Storage};

/// The bound `cas()`'s internal retry loop honors for a definitely-non-
/// mismatch ref-update failure (SG19a): give up and return
/// [`GitStorageError::RefUpdateTransient`] once this much wall-clock time
/// has elapsed since the first attempt, rather than retrying forever. A
/// genuine compare-mismatch is never retried internally regardless of this
/// bound -- it returns [`GitStorageError::TipMoved`] on the first attempt.
const RETRY_BOUND: Duration = Duration::from_secs(2);

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
    /// `load_log_meta` (below) reports `None` exactly when this is `None`,
    /// so a repository that hosts several logs side by side, each under its
    /// own staging ref (e.g. a fork: sealing one ref and resuming into a
    /// brand-new ref in the same repository), reports freshness correctly
    /// per ref -- one ref's committed log is never visible through another.
    observed_tip: Option<ObjectId>,
    count: u64,
    kind_byte: u8,
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
        let (observed_tip, count, kind_byte) = match local
            .try_find_reference(staging_ref.as_ref())
            .map_err(|e| GitStorageError::Git(e.to_string()))?
        {
            None => (None, 0, 0),
            Some(mut r) => {
                let tree_id = r
                    .peel_to_id()
                    .map_err(|e| GitStorageError::Git(e.to_string()))?
                    .detach();
                let meta_id = gitutil::find_entry(&local, tree_id, "meta")?.ok_or_else(|| {
                    GitStorageError::Corruption("staging ref's tree has no meta".into())
                })?;
                let bytes = gitutil::read_blob(&local, meta_id)?;
                let (stored_arity, count, kind_byte) = layout::decode_meta(&bytes)?;
                if stored_arity != arity {
                    return Err(GitStorageError::InvalidArity(format!(
                        "instance arity {arity} disagrees with stored meta.arity {stored_arity}"
                    )));
                }
                (Some(tree_id), count, kind_byte)
            },
        };

        Ok(Self {
            repo,
            staging_ref,
            arity,
            observed_tip,
            count,
            kind_byte,
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
        let (_arity, count, _kind) = layout::decode_meta(&bytes)?;
        Ok(GitReadOnlyView {
            repo: self.repo.clone(),
            tree,
            size: count,
        })
    }

    fn thread_local(&self) -> gix::Repository {
        self.repo.to_thread_local()
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

    async fn store_leaf(&mut self, index: u64, data: &[u8]) -> Result<(), Self::Error> {
        if index != self.count {
            return Err(GitStorageError::Corruption(format!(
                "store_leaf: out-of-order index {index}, expected {}",
                self.count
            )));
        }
        self.write_batch(
            &[(index, data)],
            &[],
            &[],
            Some((index + 1, self.kind_byte)),
            &[],
        )
        .await
    }

    async fn get_leaf(&self, index: u64) -> Result<Vec<u8>, Self::Error> {
        let Some(tree) = self.observed_tip else {
            return Err(GitStorageError::NotFound(format!(
                "leaf index {index} (empty store)"
            )));
        };
        let repo = self.thread_local();
        read::get_leaf(&repo, tree, self.count, index)
    }

    async fn len(&self) -> Result<u64, Self::Error> {
        Ok(self.count)
    }

    async fn store_node(
        &mut self,
        alg_id: u64,
        left: u64,
        height: u32,
        hash: &[u8],
    ) -> Result<(), Self::Error> {
        self.write_batch(&[], &[(alg_id, left, height, hash)], &[], None, &[])
            .await
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

    async fn store_algorithm_meta(
        &mut self,
        alg_id: u64,
        epochs: &[(u64, u64)],
    ) -> Result<(), Self::Error> {
        self.write_batch(&[], &[], &[(alg_id, epochs)], None, &[])
            .await
    }

    async fn load_algorithm_metas(&self) -> Result<AlgorithmMetas, Self::Error> {
        let Some(tree) = self.observed_tip else {
            return Ok(Vec::new());
        };
        let repo = self.thread_local();
        read::load_algorithm_metas(&repo, tree)
    }

    async fn load_log_meta(&self) -> Result<Option<(u64, u8)>, Self::Error> {
        Ok(self.observed_tip.map(|_| (self.count, self.kind_byte)))
    }

    async fn load_checkpoint_roots(&self) -> Result<Vec<(u64, Vec<u8>)>, Self::Error> {
        let Some(tree) = self.observed_tip else {
            return Ok(Vec::new());
        };
        let repo = self.thread_local();
        read::load_checkpoint_roots(&repo, tree)
    }

    async fn write_batch(
        &mut self,
        leaves: &[(u64, &[u8])],
        nodes: &[(u64, u64, u32, &[u8])],
        algorithm_metas: &[(u64, &[(u64, u64)])],
        log_meta: Option<(u64, u8)>,
        checkpoint_roots: &[(u64, &[u8])],
    ) -> Result<(), Self::Error> {
        let repo = self.thread_local();
        let input = build::WriteInputs {
            leaves,
            nodes,
            algorithm_metas,
            log_meta,
            checkpoint_roots,
        };
        let old = build::OldState {
            tree: self.observed_tip,
            count: self.count,
            kind: self.kind_byte,
        };
        let applied = build::apply_write(&repo, self.arity, old, &input)?;
        self.cas(&repo, applied.tree_id)?;
        self.observed_tip = Some(applied.tree_id);
        self.count = applied.count;
        self.kind_byte = applied.kind_byte;
        Ok(())
    }
}

/// A read-only view over one checkpoint tree, returned by
/// [`GitStorage::open_at`] (§4.4, SG21). Exposes exactly the trait's read
/// methods that make sense against a frozen historical tree; carries no
/// mutation and no dependency on the instance that produced it.
pub struct GitReadOnlyView {
    repo: gix::ThreadSafeRepository,
    tree: ObjectId,
    size: u64,
}

impl GitReadOnlyView {
    /// The checkpoint tree this view reads from.
    #[must_use]
    pub fn tree(&self) -> ObjectId {
        self.tree
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
