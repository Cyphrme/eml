//! Git-backed storage backend for the EML append-only library.
//!
//! Implements `polydigest`'s [`Storage`] trait over a git object database
//! reached through `gix`, per `docs/specs/storage-git.md`. Git is mere
//! storage here: nothing in this crate trusts a git object id as a security
//! boundary, and no hash algorithm is ever named (SG26) -- every digest this
//! layer persists is caller-supplied bytes, and it queries
//! `Repository::object_hash()` rather than assuming SHA-1 or SHA-256 (SG27).
//!
//! # Departures from the spec's literal text
//!
//! 1. **Arity is a constructor parameter, not trait-carried.** `Storage` never passes `k`; the
//!    checkpoint tree's layout (§2) is parametric in it throughout. [`GitStorage::new`] takes
//!    `arity` explicitly and persists it in `meta` (SG12); reopening against a tree whose stored
//!    arity disagrees is rejected as [`GitStorageError::InvalidArity`].
//! 2. **Standalone `store_leaf`/`store_node` require in-order coordinates, and never complete a
//!    merge on their own.** Unlike `storage-fjall`'s sparse-friendly flat keyspace, this layer's
//!    positional layout is built on aligned blocks sealed in order (SG8); a standalone
//!    `store_leaf(index, _)` is accepted only at `index == len()`, matching the same append-only
//!    assumption `MemoryStorage` already makes via its own `debug_assert_eq!`. Further, because
//!    neither standalone method carries a hasher, if `index` would complete a `k`-ary merge (a
//!    carry reduction), this layer has no digest to seal the merged parent with and the write fails
//!    with `Corruption` -- `polydigest` never actually calls either method standalone for a
//!    count-changing append (it always goes through `write_batch`, which carries the combinator's
//!    own computed node digests alongside the leaf); this limitation is only reachable by a caller
//!    driving the trait directly, bypassing the combinator.
//! 3. **`get_node` is scoped to peaks and their descendants, decomposed once every child slot has a
//!    known occupant (§2.6, §2.7, SG28/SG29).** An earlier revision built a taller peak opaque
//!    (`digest/` only, no children at all) the moment *any* child it would need to attach was not
//!    fully materialized -- which silently dropped a materialized descendant sitting right next to
//!    an opaque one, permanently, the instant its parent left `peaks/`; a side `inherited/` archive
//!    patched around that loss for the one case it *could* still recover (a coordinate that had
//!    itself once been a peak). `build::resolve_node` now wires a `hex(c,2)` child entry for every
//!    slot at once, as soon as this layer has a known occupant for *all* of them -- opaque or
//!    materialized, reused by object id (SG18a) or freshly built -- never gated on whether a known
//!    occupant is itself opaque, so a coordinate that was ever a frontier peak stays reachable by
//!    ordinary descent from whatever taller peak now covers it, for the life of the log, with no
//!    side archive at all: `C(n)`'s four top-level entries (SG1) are unconditional now, for every
//!    log, resumed or not. Only a coordinate strictly *beneath* a leaf-level opaque node (`h = 0`,
//!    no `leaf` blob, SG4) -- one that was never itself a peak and so was never given a digest of
//!    its own -- remains unreconstructable, since nothing was ever there to decompose. A related,
//!    narrower case in the same area: a frontier coordinate every covering algorithm has already
//!    been removed from (so `write_batch` is handed no digest for it by anyone, most reachably
//!    through `polydigest::NaryMerkleLog::resume`'s per-algorithm epoch gate) is built as an
//!    empty-`digest/`, opaque node rather than rejected as `Corruption` -- a legitimate frontier
//!    position with nothing live behind it, not a missing-data bug. See `src/build.rs` and
//!    `src/read.rs` for the full argument.
//! 4. **A resumption's storage MUST be fresh, so a resumed seal's opacity is decided purely by what
//!    is stored plus what the write supplies.** `polydigest::NaryMerkleLog::resume` refuses a
//!    `storage` that already carries a committed log of its own (`Storage::load_log_meta` returns
//!    `Some`), before anything is written -- a resumption's genesis frontier is not a way to reopen
//!    or splice onto an existing log's committed state (`polydigest/src/tree.rs`'s `resume`). That
//!    refusal is what removes the only case in which this layer would otherwise need to distinguish
//!    "the caller is genuinely resuming a seal" from "the caller merely reopened a continuing log":
//!    a resumption's target is always empty, so its first write's touched coordinates never carry a
//!    stale, differently-provisioned occupant to starve -- there is nothing there to begin with.
//!    Every write, resuming or continuing, therefore follows the one rule: a touched coordinate
//!    carries its prior digests, leaf, and children forward from whatever this same log's own
//!    history already gave it (§2.6, SG10/SG11), with no separate resume-open constructor and no
//!    committed provenance field needed to tell the two cases apart.
//!
//! # The tip-tree model
//!
//! This layer keeps the **complete** checkpoint tree behind its staging ref: every leaf and
//! sealed node ever written, by coordinate, forever (§2.6-§2.7). The staging ref always points
//! **directly at a tree object** (never a commit), and [`GitStorage::tip_tree`] hands that object
//! id back verbatim. This layer never creates a commit and never renders or reconstructs a tree
//! for a size other than its current one: a past size is read by wrapping an earlier tip tree in
//! a commit one layer up (the checkpoint library this crate is deliberately ignorant of), and by
//! `eml` reading over the nodes the complete tip tree already contains.

mod build;
mod error;
mod gitutil;
mod layout;
mod read;

use std::path::Path;

pub use error::GitStorageError;
use gix::ObjectId;
use gix::refs::transaction::{Change, LogChange, PreviousValue, RefEdit};
use gix::refs::{FullName, Target};
use polydigest::{AlgorithmMetas, Storage};

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

    /// The current tip: the complete checkpoint tree the staging ref points
    /// at right now, or `None` for a fresh instance whose ref has never been
    /// written (genesis).
    ///
    /// This is a pure read of [`Self::new`]'s last-observed value (or the
    /// value a subsequent write left behind) -- never a reconstruction, and
    /// never anything other than the current `C(n)`. The checkpoint layer
    /// above this crate commits this tree to anchor it; this crate itself
    /// never renders or reconstructs a tree for any other size (see "The
    /// tip-tree model" above).
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
        let (stored_arity, count, _kind) = layout::decode_meta(&bytes)?;
        Ok(GitReadOnlyView {
            repo: self.repo.clone(),
            tree,
            arity: stored_arity,
            size: count,
        })
    }

    fn thread_local(&self) -> gix::Repository {
        self.repo.to_thread_local()
    }

    fn cas(&self, repo: &gix::Repository, new_tree: ObjectId) -> Result<(), GitStorageError> {
        let expected = match self.observed_tip {
            Some(id) => PreviousValue::MustExistAndMatch(Target::Object(id)),
            None => PreviousValue::MustNotExist,
        };
        let edit = RefEdit {
            change: Change::Update {
                log: LogChange::default(),
                expected,
                new: Target::Object(new_tree),
            },
            name: self.staging_ref.clone(),
            deref: false,
        };
        match repo.edit_reference(edit) {
            Ok(_) => Ok(()),
            Err(_) => {
                let actual = repo
                    .try_find_reference(self.staging_ref.as_ref())
                    .ok()
                    .flatten()
                    .map(|r| r.target().id().to_owned().to_string());
                Err(GitStorageError::TipMoved {
                    expected: self.observed_tip.map(|id| id.to_string()),
                    actual,
                })
            },
        }
    }
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
        read::get_leaf(&repo, tree, self.arity, self.count, index)
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
        read::get_node(&repo, tree, self.arity, self.count, alg_id, left, height)
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
    arity: u64,
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
        read::get_leaf(&repo, self.tree, self.arity, self.size, index)
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
        read::get_node(
            &repo, self.tree, self.arity, self.size, alg_id, left, height,
        )
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
