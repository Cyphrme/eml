//! Shared fixtures for the independent acceptance suite in
//! `storage-git/tests/acceptance_*.rs`.
//!
//! Written from `docs/specs/storage-git.md` alone, without reading
//! `storage-git`'s own test helpers (`tests/common/mod.rs`) or any of its
//! private modules' bodies. Only `storage-git`'s public API
//! (`storage_git::{GitStorage, GitStorageError, GitReadOnlyView}`) and the
//! public API of its already-complete sibling crates (`polydigest`, `spine`,
//! `cml` — named by the spec itself as reference oracles, e.g. SG8's
//! `MemoryStorage` comparison and SG13's `epochs_at` comparison) are used
//! here.
//!
//! Not itself a test binary: it lives in a subdirectory of `tests/`, so
//! Cargo does not compile it as a standalone integration-test crate: each
//! `acceptance_*.rs` file pulls it in with
//! `#[path = "acceptance_support/mod.rs"] mod support;`.
#![allow(dead_code)]

use std::path::Path;
use std::time::SystemTime;

use polydigest::{MemoryStorage, NaryMerkleLog, Storage, TreeConfig, WriteOp};
use spine::Hasher;
use storage_git::{GitStorage, GitStorageError};

/// Append one raw leaf directly through [`Storage::apply`], with no node or
/// checkpoint-root side effects -- the direct-`Storage`-level equivalent of
/// the old standalone `store_leaf`, for tests exercising `GitStorage`'s CAS
/// behavior below the `NaryMerkleLog` layer.
#[allow(dead_code)]
pub async fn append_leaf(
    storage: &mut GitStorage,
    index: u64,
    data: &[u8],
) -> Result<(), GitStorageError> {
    storage
        .apply(&[WriteOp::AppendLeaf {
            at: index,
            data,
            nodes: &[],
            checkpoint_roots: &[],
        }])
        .await
}

/// Register one algorithm directly through [`Storage::apply`] -- the
/// direct-`Storage`-level equivalent of the old standalone
/// `store_algorithm_meta`.
#[allow(dead_code)]
pub async fn add_algorithm_meta(
    storage: &mut GitStorage,
    alg_id: u64,
    epochs: &[(u64, u64)],
) -> Result<(), GitStorageError> {
    storage
        .apply(&[WriteOp::AddAlgorithm { alg_id, epochs }])
        .await
}

/// A caller-supplied hasher fixture (SG26: this crate's tests may hardcode a
/// concrete hasher; `storage-git` itself never may). Backed by SHA-256,
/// truncated to `width` bytes so the same fixture can exercise more than one
/// digest width (SG26/SG27's parametrization requirement).
#[derive(Debug, Clone)]
pub struct FixtureHasher {
    pub width: usize,
}

impl FixtureHasher {
    #[must_use]
    pub fn new(width: usize) -> Self {
        assert!(
            (1..=32).contains(&width),
            "fixture hasher width must fit in a SHA-256 output"
        );
        Self { width }
    }
}

impl Hasher for FixtureHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        self.hash(data)
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut buf = Vec::new();
        for c in children {
            buf.extend_from_slice(c);
        }
        self.hash(&buf)
    }

    fn empty(&self) -> Vec<u8> {
        self.hash(b"")
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        h.update(data);
        h.finalize()[..self.width].to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(self.clone())
    }
}

/// The two object-hash formats SG27 requires this crate to work under.
#[must_use]
pub fn object_hash_formats() -> Vec<gix::hash::Kind> {
    vec![gix::hash::Kind::Sha1, gix::hash::Kind::Sha256]
}

/// Two `Hasher` fixtures of different digest widths, for SG26/SG27's
/// "parametrized over more than one `Hasher` implementation" requirement.
#[must_use]
pub fn hasher_widths() -> Vec<usize> {
    vec![32, 20]
}

/// Create a fresh bare repository at `dir` under the given git object-hash
/// format.
#[must_use]
pub fn bare_repo(dir: &Path, object_hash: gix::hash::Kind) -> gix::ThreadSafeRepository {
    gix::ThreadSafeRepository::init_opts(
        dir,
        gix::create::Kind::Bare,
        gix::create::Options {
            object_hash: Some(object_hash),
            ..Default::default()
        },
        gix::open::Options::default(),
    )
    .expect("init bare repository")
}

/// Reopen an existing repository at `dir` (used to build a second,
/// independent `GitStorage` instance against the same on-disk repository —
/// e.g. two concurrent writers for SG17-19, or a corrupted-fixture writer for
/// SG15).
#[must_use]
pub fn reopen_repo(dir: &Path) -> gix::ThreadSafeRepository {
    gix::ThreadSafeRepository::open(dir).expect("reopen repository")
}

/// `hex(x, w)` per the spec's own notation (§1).
#[must_use]
pub fn hex(x: u64, w: usize) -> String {
    format!("{x:0w$x}")
}

/// One entry read directly out of a decoded git tree, independent of
/// `storage-git`'s own decoding.
#[derive(Debug, Clone)]
pub struct RawEntry {
    pub name: String,
    pub mode: gix::objs::tree::EntryMode,
    pub oid: gix::ObjectId,
}

/// Decode a tree object's direct children, in the order git stored them (no
/// re-sorting here — SG6/SG7 tests want to see storage order as written).
#[must_use]
pub fn read_tree(repo: &gix::Repository, tree: gix::ObjectId) -> Vec<RawEntry> {
    let t = repo
        .find_tree(tree)
        .unwrap_or_else(|e| panic!("{tree}: not a tree: {e}"));
    let decoded = t.decode().expect("tree decodes");
    decoded
        .entries
        .iter()
        .map(|e| RawEntry {
            name: e.filename.to_string(),
            mode: e.mode,
            oid: e.oid.to_owned(),
        })
        .collect()
}

/// Find one named entry directly under `tree`, or `None`.
#[must_use]
pub fn find_entry(repo: &gix::Repository, tree: gix::ObjectId, name: &str) -> Option<RawEntry> {
    read_tree(repo, tree).into_iter().find(|e| e.name == name)
}

/// Resolve a `/`-separated git path from `tree`, returning the final entry.
#[must_use]
pub fn resolve_path(repo: &gix::Repository, tree: gix::ObjectId, path: &str) -> Option<RawEntry> {
    let mut current = tree;
    let mut last: Option<RawEntry> = None;
    for component in path.split('/') {
        let entry = find_entry(repo, current, component)?;
        current = entry.oid;
        last = Some(entry);
    }
    last
}

/// Read a blob's raw bytes.
#[must_use]
pub fn read_blob(repo: &gix::Repository, id: gix::ObjectId) -> Vec<u8> {
    repo.find_blob(id)
        .unwrap_or_else(|e| panic!("{id}: not a blob: {e}"))
        .data
        .clone()
}

/// The current staging-ref target, read directly via `gix` (never through
/// `storage-git`'s own API), or `None` if the ref does not exist yet.
#[must_use]
pub fn ref_target(repo: &gix::Repository, staging_ref: &str) -> Option<gix::ObjectId> {
    let r = repo.try_find_reference(staging_ref).expect("ref lookup");
    r.map(|r| match r.target() {
        gix::refs::TargetRef::Object(id) => id.to_owned(),
        gix::refs::TargetRef::Symbolic(_) => panic!("staging ref must never be symbolic (SG17)"),
    })
}

/// The kind of the object a tree/blob-agnostic id resolves to.
#[must_use]
pub fn object_kind(repo: &gix::Repository, id: gix::ObjectId) -> gix::objs::Kind {
    repo.find_object(id).expect("object exists").kind
}

/// Recursively walk every object a checkpoint tree (or any of its
/// descendants) references, panicking if any is missing — the outward
/// consequence SG23 requires ("every object the batch newly references is
/// still present") and a component of SG9/SG20's reconstructibility.
pub fn assert_fully_reachable(repo: &gix::Repository, root: gix::ObjectId) {
    let obj = repo
        .try_find_object(root)
        .expect("odb read")
        .unwrap_or_else(|| panic!("missing object: {root}"));
    if obj.kind == gix::objs::Kind::Tree {
        for entry in read_tree(repo, root) {
            assert_fully_reachable(repo, entry.oid);
        }
    }
}

/// The on-disk path of a loose object, for the two crates under test that
/// observe git's own filesystem freshening behavior (SG22/SG23). Only valid
/// for a bare repository backed by loose (unpacked) objects, which is what a
/// freshly `bare_repo`-initialized fixture always is.
#[must_use]
pub fn loose_object_path(git_dir: &Path, id: gix::ObjectId) -> std::path::PathBuf {
    let hex = id.to_string();
    git_dir.join("objects").join(&hex[0..2]).join(&hex[2..])
}

/// The loose object file's current mtime, or `None` if it is not a loose
/// file on disk (e.g. already packed).
#[must_use]
pub fn loose_object_mtime(git_dir: &Path, id: gix::ObjectId) -> Option<SystemTime> {
    std::fs::metadata(loose_object_path(git_dir, id))
        .ok()?
        .modified()
        .ok()
}

/// Age a loose object's mtime far into the past, so a later re-touch is
/// unambiguously detectable.
pub fn age_loose_object(git_dir: &Path, id: gix::ObjectId) {
    let path = loose_object_path(git_dir, id);
    let ancient = SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(60 * 60 * 24 * 365);
    let file =
        std::fs::File::open(&path).unwrap_or_else(|e| panic!("open {}: {e}", path.display()));
    let times = std::fs::FileTimes::new().set_modified(ancient);
    file.set_times(times)
        .unwrap_or_else(|e| panic!("set_times {}: {e}", path.display()));
}

/// Build a fresh `NaryMerkleLog<GitStorage>` at `staging_ref` inside `repo`,
/// with algorithm `0` registered under `hasher`.
pub async fn new_log(
    repo: &gix::ThreadSafeRepository,
    staging_ref: &str,
    arity: u64,
    hasher: FixtureHasher,
) -> NaryMerkleLog<storage_git::GitStorage> {
    let storage =
        storage_git::GitStorage::new(repo.clone(), staging_ref, arity).expect("open GitStorage");
    NaryMerkleLog::new(storage, Box::new(hasher), TreeConfig { arity })
        .await
        .expect("new log")
}

/// A `MemoryStorage`-backed reference log, driven through the identical
/// operation sequence a `GitStorage`-backed log under test receives, for the
/// property tests the spec itself prescribes (SG8's table entry: "Property
/// tests comparing this backend's reads against `MemoryStorage`").
pub async fn new_memory_log(arity: u64, hasher: FixtureHasher) -> NaryMerkleLog<MemoryStorage> {
    NaryMerkleLog::new(MemoryStorage::new(), Box::new(hasher), TreeConfig { arity })
        .await
        .expect("new memory log")
}
