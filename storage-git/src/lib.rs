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
//! 3. **`get_node`/`tree_at` are scoped to peaks and their descendants, decomposed once every child
//!    slot has a known occupant (§2.6, §2.7, SG28/SG29).** An earlier revision built a taller peak
//!    opaque (`digest/` only, no children at all) the moment *any* child it would need to attach
//!    was not fully materialized -- which silently dropped a materialized descendant sitting right
//!    next to an opaque one, permanently, the instant its parent left `peaks/`; a side `inherited/`
//!    archive patched around that loss for the one case it *could* still recover (a coordinate that
//!    had itself once been a peak). `build::resolve_node` now wires a `hex(c,2)` child entry for
//!    every slot at once, as soon as this layer has a known occupant for *all* of them -- opaque or
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
//!    position with nothing live behind it, not a missing-data bug. See `src/build.rs`,
//!    `src/read.rs`, and `src/historical.rs` for the full argument.
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
//! 5. **`tree_at(n)` for `n < len()` needs a registered hasher to fold `roots/` correctly, and
//!    never returns a tree other than `C(n)` (SG20's amendment).** A past member root needs the
//!    algorithm's hash fold over its historical frontier peaks; [`GitStorage::register_hasher`]
//!    lets a caller supply that fold (an opaque `spine::Hasher` trait object, keyed by the same
//!    opaque `alg_id` every other method already uses -- SG26 names no algorithm regardless).
//!    Omitting an active algorithm's `roots/` entry when no hasher was registered for it would
//!    return a well-formed but wrong tree a consumer could not tell from the genuine one, so
//!    `tree_at` returns an error naming the algorithm instead of `Ok`. A registered hasher is
//!    likewise trusted only on stored evidence: it is rejected before any historical root is
//!    trusted if it fails to reproduce a digest this layer already has on file for it, and an
//!    algorithm with no such evidence anywhere -- nothing materialized to recompute, and fewer than
//!    two frontier peaks to fold -- is refused outright rather than silently trusted, but only
//!    where reconstructing the requested `n` would actually need that trust: never for `n` equal to
//!    the current size served as the staging tip, and never for a target frontier of zero or one
//!    peak, since a fold is only ever needed to combine two or more peaks. See `src/historical.rs`.

mod build;
mod error;
mod gitutil;
mod historical;
mod layout;
mod read;

use std::collections::HashMap;
use std::path::Path;

pub use error::GitStorageError;
use gix::ObjectId;
use gix::refs::transaction::{Change, LogChange, PreviousValue, RefEdit};
use gix::refs::{FullName, Target};
use polydigest::{AlgorithmMetas, Storage};
use spine::Hasher;

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
    /// Per-algorithm hash folds registered via [`Self::register_hasher`],
    /// consulted only by [`Self::tree_at`] to reconstruct a historical
    /// `roots/` entry (§4.3, SG20). Empty by default -- this crate never
    /// assumes or requires one (SG26).
    hashers: HashMap<u64, Box<dyn Hasher>>,
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
            hashers: HashMap::new(),
        })
    }

    /// Register `hasher` as `alg_id`'s fold, for [`Self::tree_at`]'s
    /// historical `roots/` reconstruction only (§4.3, SG20 amendment).
    ///
    /// Names no algorithm to this crate (SG26): `hasher` is an opaque
    /// `spine::Hasher` trait object the caller owns and chooses, keyed by
    /// the same opaque `alg_id` every other method already treats it as. A
    /// `tree_at(n)` call for an algorithm active at `n` with no hasher
    /// registered here -- or with one that cannot be verified against any
    /// stored evidence -- returns an error naming the algorithm rather than
    /// fabricating or silently omitting its `roots/hex(alg_id,16)` entry.
    pub fn register_hasher(&mut self, alg_id: u64, hasher: Box<dyn Hasher>) {
        self.hashers.insert(alg_id, hasher);
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

    /// `C(n)`'s object id for any `n` from `0` to this instance's current
    /// size, inclusive (§4.3, SG20).
    ///
    /// # Errors
    ///
    /// Returns [`GitStorageError::Corruption`] if `n` exceeds the current
    /// size, if a historical coordinate below `n` is not reconstructable
    /// (Departure 3 above: a coordinate strictly beneath a leaf-level opaque
    /// node that was never itself a peak), if an
    /// algorithm active at `n` has no hasher registered, or if a registered
    /// hasher cannot be trusted -- because it fails to reproduce a digest
    /// this layer already has on file for it, or because reconstructing `n`
    /// actually needs to fold two or more peaks together and no stored
    /// evidence exists anywhere to check it against (Departure 5 above,
    /// SG20's amendment).
    pub fn tree_at(&self, n: u64) -> Result<ObjectId, GitStorageError> {
        if n > self.count {
            return Err(GitStorageError::Corruption(format!(
                "tree_at({n}): exceeds current size {}",
                self.count
            )));
        }
        let repo = self.repo.to_thread_local();
        if let Some(tree) = self.observed_tip {
            historical::validate_hashers(&repo, self.arity, tree, self.count, n, &self.hashers)?;
        }
        if n == self.count {
            if let Some(id) = self.observed_tip {
                return Ok(id);
            }
        }
        let current = historical::CurrentState {
            tree: self.observed_tip,
            size: self.count,
            kind_byte: self.kind_byte,
        };
        historical::reconstruct(&repo, self.arity, current, n, &self.hashers)
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
