//! Shared test fixtures: repository setup and two `Hasher` implementations
//! of different digest widths (SG26), used across this crate's structural,
//! differential, and parametric tests.

use std::collections::HashSet;

use gix::ThreadSafeRepository;
use gix::create::{Kind as CreateKind, Options as CreateOptions};
use gix::hash::Kind as HashKind;
use sha2::{Digest, Sha256};
use spine::Hasher;
use tempfile::TempDir;

/// Initialize a fresh bare repository under the requested object-hash
/// format (SG27).
#[must_use]
pub fn init_repo(hash: HashKind) -> (TempDir, ThreadSafeRepository) {
    let dir = tempfile::tempdir().unwrap();
    let opts = CreateOptions {
        object_hash: Some(hash),
        ..Default::default()
    };
    let repo =
        ThreadSafeRepository::init_opts(dir.path(), CreateKind::Bare, opts, Default::default())
            .expect("init bare repository");
    (dir, repo)
}

/// A 32-byte SHA-256 hasher, the same shape `storage-fjall`'s own tests use.
///
/// `allow(dead_code)`: this module is compiled once per integration test
/// binary, and not every binary that uses one hasher also uses the other.
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub struct WideHasher;

impl Hasher for WideHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for c in children {
            h.update(c);
        }
        h.finalize().to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"").to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data).to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(WideHasher)
    }
}

/// An 8-byte hasher (SHA-256 truncated), deliberately a different width
/// than [`WideHasher`] so SG26's width-parametricity claim is exercised by
/// at least two distinct widths, never assumed to be 32.
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub struct NarrowHasher;

impl Hasher for NarrowHasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data)[..8].to_vec()
    }

    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for c in children {
            h.update(c);
        }
        h.finalize()[..8].to_vec()
    }

    fn empty(&self) -> Vec<u8> {
        Sha256::digest(b"")[..8].to_vec()
    }

    fn hash(&self, data: &[u8]) -> Vec<u8> {
        Sha256::digest(data)[..8].to_vec()
    }

    fn clone_box(&self) -> Box<dyn Hasher> {
        Box::new(NarrowHasher)
    }
}

// ============================================================================
// Generic git-tree helpers and the byte1-be-trim key path scheme (the
// ratified key-derived layout, per `spike-report.md`'s recommendation).
// Added independently of
// `acceptance_support/mod.rs`, which is deliberately written from the spec
// alone and never shares helpers with this module.
// ============================================================================

/// One entry read directly out of a decoded git tree, independent of
/// `storage-git`'s own decoding.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct RawEntry {
    pub name: String,
    pub mode: gix::objs::tree::EntryMode,
    pub oid: gix::ObjectId,
}

/// Decode a tree object's direct children, in git's own stored (already
/// canonically sorted) order.
#[must_use]
#[allow(dead_code)]
pub fn read_tree_entries(repo: &gix::Repository, tree: gix::ObjectId) -> Vec<RawEntry> {
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
#[allow(dead_code)]
pub fn find_child(repo: &gix::Repository, tree: gix::ObjectId, name: &str) -> Option<RawEntry> {
    read_tree_entries(repo, tree)
        .into_iter()
        .find(|e| e.name == name)
}

/// Resolve a sequence of path segments from `tree`, returning the final
/// entry, or `None` if any segment along the way is missing.
#[must_use]
#[allow(dead_code)]
pub fn resolve_segments(
    repo: &gix::Repository,
    tree: gix::ObjectId,
    segments: &[String],
) -> Option<RawEntry> {
    let mut current = tree;
    let mut last: Option<RawEntry> = None;
    for seg in segments {
        let entry = find_child(repo, current, seg)?;
        current = entry.oid;
        last = Some(entry);
    }
    last
}

/// Enumerate every `/`-joined path from `tree` down to a terminal (non-tree)
/// entry -- a pure path-driven walk, never deduplicated by object id, so a
/// coincidentally shared subtree object (e.g. two dedup'd identical blobs)
/// is still enumerated once per path that reaches it. Depth is bounded by
/// the key schemes this crate's tests drive (at most ~11 segments), so no
/// cycle guard is needed: a git tree is acyclic by construction.
#[allow(dead_code)]
pub fn enumerate_full_paths(repo: &gix::Repository, tree: gix::ObjectId) -> HashSet<String> {
    fn walk(
        repo: &gix::Repository,
        tree: gix::ObjectId,
        prefix: &mut Vec<String>,
        out: &mut HashSet<String>,
    ) {
        for e in read_tree_entries(repo, tree) {
            prefix.push(e.name.clone());
            if e.mode.is_tree() {
                walk(repo, e.oid, prefix, out);
            } else {
                out.insert(prefix.join("/"));
            }
            prefix.pop();
        }
    }
    let mut out = HashSet::new();
    walk(repo, tree, &mut Vec::new(), &mut out);
    out
}

/// The largest number of direct entries any tree object reachable from
/// `tree` carries -- the empirical form of "no tree object exceeds 256
/// entries" (spike-report.md's confirmed `byte1-be-trim` bound).
#[must_use]
#[allow(dead_code)]
pub fn max_tree_width_recursive(repo: &gix::Repository, tree: gix::ObjectId) -> usize {
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![tree];
    let mut widest = 0usize;
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        if repo.find_tree(id).is_ok() {
            let entries = read_tree_entries(repo, id);
            widest = widest.max(entries.len());
            for e in &entries {
                if e.mode.is_tree() {
                    stack.push(e.oid);
                }
            }
        }
    }
    widest
}

/// The `byte1-be-trim` path scheme `spike-report.md` recommends and
/// `storage-git-keyed::PathScheme::TrimmedFanout{width:1}`
/// (`.worktrees/spike-key-layout/storage-git-keyed/src/pathscheme.rs`)
/// implements: a numeric key's leading zero bytes are stripped, a one-ASCII-
/// digit length segment (the count of remaining significant bytes, `1..=8`)
/// is prepended, and each remaining byte becomes its own two-lowercase-hex-
/// digit segment, most-significant byte first. `key == 0` is one
/// significant (zero) byte, never zero segments, so every key gets a
/// non-empty path. Ported test-for-test against
/// `storage-git-keyed::pathscheme::tests` below.
#[must_use]
#[allow(dead_code)]
pub fn trimmed_key_segments(key: u64) -> Vec<String> {
    let be = key.to_be_bytes();
    let first_nonzero = be.iter().position(|&b| b != 0).unwrap_or(7);
    let sig = &be[first_nonzero..];
    let mut segs = vec![sig.len().to_string()];
    segs.extend(sig.iter().map(|b| format!("{b:02x}")));
    segs
}

/// The inverse of [`trimmed_key_segments`]: given the segments found under a
/// `byte1-be-trim` path (the length digit plus its hex-pair bytes),
/// reconstruct the original `u64` key, or `None` if the segments are not a
/// well-formed encoding (wrong count, non-hex byte, out-of-range length).
/// Used by the reverse-completeness property to turn git's own actual
/// stored paths back into keys comparable against an independent oracle's
/// key set -- the direction [`trimmed_key_segments`] alone cannot check.
#[must_use]
#[allow(dead_code)]
pub fn untrim_key_segments(segs: &[&str]) -> Option<u64> {
    let (len_seg, byte_segs) = segs.split_first()?;
    let len: usize = len_seg.parse().ok()?;
    if !(1..=8).contains(&len) || byte_segs.len() != len {
        return None;
    }
    let mut buf = [0u8; 8];
    let start = 8 - len;
    for (i, seg) in byte_segs.iter().enumerate() {
        buf[start + i] = u8::from_str_radix(seg, 16).ok()?;
    }
    Some(u64::from_be_bytes(buf))
}

/// Decode a `/`-joined path found under the top-level `n` namespace
/// (`<hex16(alg_id)>/<hex2(height)>/<trimmed(left)...>`) back into
/// `(alg_id, left, height)`, or `None` if it is not well-formed.
#[must_use]
#[allow(dead_code)]
pub fn decode_node_path(path: &str) -> Option<(u64, u64, u32)> {
    let segs: Vec<&str> = path.split('/').collect();
    let (alg_seg, rest) = segs.split_first()?;
    let (height_seg, key_segs) = rest.split_first()?;
    let alg_id = u64::from_str_radix(alg_seg, 16).ok()?;
    let height = u32::from_str_radix(height_seg, 16).ok()?;
    let left = untrim_key_segments(key_segs)?;
    Some((alg_id, left, height))
}

/// Decode a `/`-joined path found under the top-level `l` namespace
/// (`<trimmed(index)...>`) back into the leaf `index`, or `None` if it is
/// not well-formed.
#[must_use]
#[allow(dead_code)]
pub fn decode_leaf_path(path: &str) -> Option<u64> {
    let segs: Vec<&str> = path.split('/').collect();
    untrim_key_segments(&segs)
}

/// `hex(x, 16)` -- a `u64` rendered as 16 lowercase hex digits, matching
/// `storage-git::layout::hex16` and `storage-git-keyed::layout::hex16`'s own
/// encoding for an algorithm id.
#[must_use]
#[allow(dead_code)]
pub fn hex16(x: u64) -> String {
    format!("{x:016x}")
}

/// `hex(x, 2)` -- a value `0..=255` rendered as 2 lowercase hex digits,
/// matching the height segment `storage-git-keyed::build::node_path` writes
/// (`format!("{height:02x}")`).
#[must_use]
#[allow(dead_code)]
pub fn hex2(x: u32) -> String {
    format!("{x:02x}")
}

// `trimmed_key_segments`'s own correctness (ported test-for-test from
// `storage-git-keyed::pathscheme::tests`) is checked once, in
// `key_derived_layout.rs`'s own `#[cfg(test)]` block -- not here, so it does
// not recompile and re-run once per `tests/*.rs` binary that pulls in this
// shared module.
