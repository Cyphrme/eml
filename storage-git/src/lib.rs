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
//! 3. **`get_node`/`tree_at` are scoped to peaks and materialized descendants.** A node sealed
//!    opaque (§2.6) that has since been folded into a taller peak carries no `hex(c,2)` children
//!    (SG4/SG10 forbid it), so nothing beneath a superseded opaque peak is addressable once it
//!    stops being the frontier's own peak; `get_node` answers `Ok(None)` and `tree_at` returns a
//!    reconstruction error for such a coordinate rather than fabricating a value. This affects
//!    subtree-kind/resumed logs at historical, already-subsumed coordinates; a flat log is never
//!    affected, since every one of its nodes is materialized all the way to its leaves. See
//!    `src/read.rs` and `src/historical.rs` for the full argument.
//! 4. **A resumed seal's opacity is a committed fact, never a process-lifetime flag (GB44).** A
//!    prior design (`has_written`) forced a `GitStorage` instance's own first `write_batch` to
//!    treat every touched coordinate as absent, so a peak inherited from a resumed seal could not
//!    silently reuse a stale, differently-provisioned occupant (SG10/SG11). The merge gate found
//!    that this made `C(n)` depend on process history: the *same* logical operations reached a
//!    different object id depending on whether the writer had reopened before its next write, and
//!    on the reopen path it also discarded another algorithm's already-stored digest and a flat
//!    node's children -- the exact SGG10/SGG11 corruption (`.ledger/deposits/git-backend/
//!    lead-maintainer/storage-git-merge-gate.md`), because an instance flag cannot distinguish "the
//!    caller is genuinely resuming a seal" from "the caller merely reopened a continuing log". That
//!    distinction cannot come from the `Storage` trait's call arguments -- `store_node` and
//!    `write_batch` look identical either way -- so it comes from which constructor opened the
//!    instance instead. [`GitStorage::open_resumed`] is the explicit resume-open: it records a
//!    resume boundary (the size the very next `write_batch` commits to) into that write's own
//!    `meta` blob (§3.1, SG12's two-shape encoding), so the boundary is a fact about the log's
//!    committed state, read back by any later plain [`GitStorage::open`]/[`GitStorage::new`], never
//!    an ephemeral property of one process's instance. Only the one write immediately following
//!    `open_resumed` treats every touched coordinate as absent (mirroring the old flag's forcing,
//!    but scoped to the caller's explicit intent rather than instance lifetime); every other write
//!    -- including a plain reopen's very first one -- carries a touched coordinate's prior digests,
//!    leaf, and children forward exactly as an ordinary continuing write does. Resuming onto a
//!    repository still holding a pre-seal instance's materialized objects and resuming onto an
//!    empty repository therefore write byte-identical trees: both starve `existing` the same way.
//! 5. **`tree_at(n)` for `n < len()` needs a registered hasher to fold `roots/` correctly, and
//!    never returns a tree other than `C(n)` (SG20's amendment, GB44).** A past member root needs
//!    the algorithm's hash fold over its historical frontier peaks; [`GitStorage::register_hasher`]
//!    lets a caller supply that fold (an opaque `spine::Hasher` trait object, keyed by the same
//!    opaque `alg_id` every other method already uses -- SG26 names no algorithm regardless). The
//!    merge gate found that the crate's former behavior -- omitting an active algorithm's `roots/`
//!    entry when no hasher was registered for it -- returned a well-formed but wrong tree, which a
//!    consumer could not tell from the genuine one (SGG12). `tree_at` now returns an error naming
//!    the algorithm instead of `Ok`, and a registered hasher is rejected before any historical root
//!    is trusted if it fails to reproduce a digest this layer already has on file for it. See
//!    `src/historical.rs`.

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
    /// The tree id this instance last observed at the staging ref, or
    /// `None` for a fresh instance whose ref has never been created
    /// (genesis; the next write's compare-and-swap uses `MustNotExist`).
    observed_tip: Option<ObjectId>,
    count: u64,
    kind_byte: u8,
    /// Per-algorithm hash folds registered via [`Self::register_hasher`],
    /// consulted only by [`Self::tree_at`] to reconstruct a historical
    /// `roots/` entry (§4.3, SG20). Empty by default -- this crate never
    /// assumes or requires one (SG26).
    hashers: HashMap<u64, Box<dyn Hasher>>,
    /// The committed resume boundary this log's `meta` currently carries
    /// (§3.1, SG12's two-shape encoding; §4.3's SG20 amendment; GB44):
    /// `Some(n)` once some write has established the log as resumed at size
    /// `n`, `None` for a log that has never been resumed. Read back from
    /// `meta` on open ([`Self::new`]/[`Self::open_resumed`]) and carried
    /// forward unchanged by every write that is not itself the
    /// resume-establishing one (see [`Self::pending_resume`]'s doc comment).
    resume_boundary: Option<u64>,
    /// Set only by [`Self::open_resumed`], and consumed by exactly this
    /// instance's next `write_batch` (build.rs::resolve_node's
    /// `force_fresh`): that one write treats every coordinate it touches as
    /// absent, regardless of what the backing repository's ref happened to
    /// point at before, and commits `resume_boundary = Some(new_count)`
    /// alongside it. A plainly opened/reopened instance ([`Self::new`],
    /// [`Self::open`]) never sets this, so its own first write behaves
    /// exactly like every later one -- the fix for the SGG10/SGG11 defect
    /// an instance-lifetime flag caused (see this module's top-level docs,
    /// departure 4).
    pending_resume: bool,
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
        let (observed_tip, count, kind_byte, resume_boundary) = match local
            .try_find_reference(staging_ref.as_ref())
            .map_err(|e| GitStorageError::Git(e.to_string()))?
        {
            None => (None, 0, 0, None),
            Some(mut r) => {
                let tree_id = r
                    .peel_to_id()
                    .map_err(|e| GitStorageError::Git(e.to_string()))?
                    .detach();
                let meta_id = gitutil::find_entry(&local, tree_id, "meta")?.ok_or_else(|| {
                    GitStorageError::Corruption("staging ref's tree has no meta".into())
                })?;
                let bytes = gitutil::read_blob(&local, meta_id)?;
                let (stored_arity, count, kind_byte, resume_boundary) =
                    layout::decode_meta(&bytes)?;
                if stored_arity != arity {
                    return Err(GitStorageError::InvalidArity(format!(
                        "instance arity {arity} disagrees with stored meta.arity {stored_arity}"
                    )));
                }
                (Some(tree_id), count, kind_byte, resume_boundary)
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
            resume_boundary,
            pending_resume: false,
        })
    }

    /// Open a `storage-git` instance exactly as [`Self::new`] does, but mark
    /// this instance's next `write_batch` as the one that establishes a
    /// resume boundary (§4.3, SG20 amendment; GB44). Use this in place of
    /// [`Self::new`]/[`Self::open`] only when the storage returned is about
    /// to be handed to a genuine seal resumption (e.g.
    /// `polydigest::NaryMerkleLog::resume`) -- never for reopening a
    /// continuing log, which must use the plain constructors so its own
    /// prior digests, leaf, and children carry forward normally (this
    /// module's top-level docs, departure 4).
    ///
    /// # Errors
    ///
    /// Identical to [`Self::new`].
    pub fn open_resumed(
        repo: gix::ThreadSafeRepository,
        staging_ref: impl AsRef<str>,
        arity: u64,
    ) -> Result<Self, GitStorageError> {
        let mut storage = Self::new(repo, staging_ref, arity)?;
        storage.pending_resume = true;
        Ok(storage)
    }

    /// Register `hasher` as `alg_id`'s fold, for [`Self::tree_at`]'s
    /// historical `roots/` reconstruction only (§4.3, SG20 amendment).
    ///
    /// Names no algorithm to this crate (SG26): `hasher` is an opaque
    /// `spine::Hasher` trait object the caller owns and chooses, keyed by
    /// the same opaque `alg_id` every other method already treats it as.
    /// A `tree_at(n)` call for an algorithm active at `n` with no hasher
    /// registered here simply omits that algorithm's
    /// `roots/hex(alg_id,16)` entry rather than fabricating or erroring.
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
    /// (Departure 3 above: an opaque node subsumed by a later merge), if an
    /// algorithm active at `n` has no hasher registered, or if a registered
    /// hasher does not reproduce a digest this layer already has on file for
    /// it (Departure 5 above, SG20's amendment, GB44).
    pub fn tree_at(&self, n: u64) -> Result<ObjectId, GitStorageError> {
        if n > self.count {
            return Err(GitStorageError::Corruption(format!(
                "tree_at({n}): exceeds current size {}",
                self.count
            )));
        }
        let repo = self.repo.to_thread_local();
        if let Some(tree) = self.observed_tip {
            historical::validate_hashers(&repo, self.arity, tree, self.count, &self.hashers)?;
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
            resume_boundary: self.resume_boundary,
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
        let (stored_arity, count, _kind, _resume_boundary) = layout::decode_meta(&bytes)?;
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
        let force_fresh = self.pending_resume;
        let old = build::OldState {
            tree: self.observed_tip,
            count: self.count,
            kind: self.kind_byte,
            resume_boundary: self.resume_boundary,
        };
        let applied = build::apply_write(&repo, self.arity, old, force_fresh, &input)?;
        self.cas(&repo, applied.tree_id)?;
        self.observed_tip = Some(applied.tree_id);
        self.count = applied.count;
        self.kind_byte = applied.kind_byte;
        self.resume_boundary = applied.resume_boundary;
        self.pending_resume = false;
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
