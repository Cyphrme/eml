//! Low-level `gix` plumbing: computing an object id under the repository's
//! own hash format and writing through the object database handle's
//! non-shortcut writer (SG22), syncing what was written to disk at a
//! checkpoint (SG31), plus the small set of read helpers the key-derived path resolution needs.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use gix::bstr::BString;
use gix::objs::{Kind, Write as _};

use crate::error::GitStorageError as Error;

fn git_err(e: impl std::fmt::Display) -> Error {
    Error::Git(e.to_string())
}

/// Compute `data`'s object id under `repo`'s own object-hash format (SG27 —
/// never a hardcoded algorithm) and write it through the object database
/// handle's `write_buf_with_known_id` (SG22): this call always performs the
/// write (no existence short-circuit), which is what refreshes an object's
/// mtime when its content happens to already exist unreferenced.
pub(crate) fn write_object(
    repo: &gix::Repository,
    kind: Kind,
    data: &[u8],
) -> Result<gix::ObjectId, Error> {
    let oid = gix::objs::compute_hash(repo.object_hash(), kind, data).map_err(git_err)?;
    repo.objects
        .write_buf_with_known_id(kind, data, oid)
        .map_err(git_err)?;
    // SG23: before considering this write durable, verify the object is
    // actually present (a header/existence check, not a full read) and
    // rewrite once if it is not -- closing the narrow window this same
    // write's own freshening (SG22) cannot, on its own, guarantee against a
    // concurrent, non-default-grace-period prune (SG24 names the residual
    // this cannot close: an immediate-expiry prune racing the gap between
    // this rewrite and the reference edit that makes the whole tree
    // reachable again).
    if !object_exists(repo, oid) {
        repo.objects
            .write_buf_with_known_id(kind, data, oid)
            .map_err(git_err)?;
        if !object_exists(repo, oid) {
            return Err(Error::Corruption(format!(
                "object {oid} missing immediately after write_buf_with_known_id (SG23)"
            )));
        }
    }
    Ok(oid)
}

/// Write a blob (SG22 write path).
pub(crate) fn write_blob(repo: &gix::Repository, data: &[u8]) -> Result<gix::ObjectId, Error> {
    write_object(repo, Kind::Blob, data)
}

/// The loose object files a checkpoint must sync, and the directories whose
/// entries name them (SG31). `gix` renames each object's tempfile into place
/// and never syncs it, nor the directory holding the new name, so until
/// [`Self::sync`] runs a power loss can drop either.
#[derive(Default)]
pub(crate) struct Unsynced {
    files: BTreeMap<PathBuf, gix::ObjectId>,
    dirs: BTreeSet<PathBuf>,
}

impl Unsynced {
    /// Record `id`'s loose file, its fan-out directory, and the objects
    /// directory (which names a fan-out directory `gix` may have just
    /// created). The path is the one `gix-odb`'s dynamic store writes to:
    /// the first loose database, which is the repository's own objects
    /// directory (`gix-odb` 0.84.0 `store_impls/dynamic/write.rs`).
    pub(crate) fn object(&mut self, repo: &gix::Repository, id: gix::ObjectId) {
        let objects = repo.objects.store_ref().path();
        let hex = id.to_hex().to_string();
        let fanout = objects.join(&hex[..2]);
        self.files.insert(fanout.join(&hex[2..]), id);
        self.dirs.insert(fanout);
        self.dirs.insert(objects.to_path_buf());
    }

    /// Sync every recorded file, then every recorded directory. A file that has vanished is
    /// tolerated only if its object still reads (a concurrent `git gc` packed it, and git syncs
    /// its own packs); a directory that has vanished held nothing left to name.
    pub(crate) fn sync(&self, repo: &gix::Repository) -> Result<(), Error> {
        for (path, id) in &self.files {
            if !sync_if_present(path)? && !object_exists(repo, *id) {
                return Err(Error::Sync(format!(
                    "object {id} vanished before its checkpoint ({})",
                    path.display()
                )));
            }
        }
        for path in &self.dirs {
            sync_if_present(path)?;
        }
        Ok(())
    }
}

/// Make the ref at `file` durable whether git holds it loose or packed
/// (SG31). `git pack-refs` writes `packed_refs` and only then deletes the
/// loose file, so a missing loose file means the value is in `packed_refs`
/// (or the ref was deleted, which is not this layer's write to protect).
/// Every directory from the ref's parent up to and including `base` is then
/// synced, since the ref update may have created any of them.
pub(crate) fn sync_ref_any_form(file: &Path, base: &Path, packed_refs: &Path) -> Result<(), Error> {
    if !sync_if_present(file)? {
        sync_if_present(packed_refs)?;
    }
    for dir in file.ancestors().skip(1) {
        sync_if_present(dir)?;
        if dir == base {
            break;
        }
    }
    Ok(())
}

#[cfg(test)]
thread_local! {
    /// Every path [`sync_path`] was asked to sync on this thread, in order
    /// -- the seam SG31's coverage test reads.
    pub(crate) static SYNCED: std::cell::RefCell<Vec<PathBuf>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// `fsync` one file or directory, reporting `false` if it does not exist. A
/// directory is synced by opening it, which is how Linux exposes durability
/// of the names a directory holds.
fn sync_if_present(path: &Path) -> Result<bool, Error> {
    #[cfg(test)]
    SYNCED.with(|s| s.borrow_mut().push(path.to_path_buf()));
    match std::fs::File::open(path).and_then(|f| f.sync_all()) {
        Ok(()) => Ok(true),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(e) => Err(Error::Sync(format!("fsync {}: {e}", path.display()))),
    }
}

/// One decoded tree entry, detached from the source tree's borrow.
#[derive(Debug, Clone)]
pub(crate) struct DecodedEntry {
    pub filename: BString,
    pub oid: gix::ObjectId,
    pub is_tree: bool,
}

/// Read and decode a tree object's entries.
pub(crate) fn read_tree(
    repo: &gix::Repository,
    id: gix::ObjectId,
) -> Result<Vec<DecodedEntry>, Error> {
    let tree = repo.find_tree(id).map_err(git_err)?;
    let decoded = tree.decode().map_err(git_err)?;
    Ok(decoded
        .entries
        .iter()
        .map(|e| DecodedEntry {
            filename: e.filename.to_owned(),
            oid: e.oid.to_owned(),
            is_tree: e.mode.is_tree(),
        })
        .collect())
}

/// Every object reachable from tree `new` but not through an identical
/// entry of tree `old`, each verified to read (a blob by header, a tree by
/// decoding). Equal subtrees are skipped unread, so the cost is the number of
/// entries in the trees that differ, never the size of the store.
pub(crate) fn changed_objects(
    repo: &gix::Repository,
    new: gix::ObjectId,
    old: Option<gix::ObjectId>,
    out: &mut Vec<gix::ObjectId>,
) -> Result<(), Error> {
    out.push(new);
    let old_entries = match old {
        Some(id) => read_tree(repo, id)?,
        None => Vec::new(),
    };
    for e in read_tree(repo, new)? {
        let twin = old_entries.iter().find(|o| o.filename == e.filename);
        if twin.is_some_and(|o| o.oid == e.oid) {
            continue;
        }
        if e.is_tree {
            changed_objects(repo, e.oid, twin.filter(|o| o.is_tree).map(|o| o.oid), out)?;
        } else if object_exists(repo, e.oid) {
            out.push(e.oid);
        } else {
            return Err(Error::Corruption(format!(
                "object {} named by a tree is missing",
                e.oid
            )));
        }
    }
    Ok(())
}

/// Find one named entry in a tree object, or `None`.
pub(crate) fn find_entry(
    repo: &gix::Repository,
    tree_id: gix::ObjectId,
    name: &str,
) -> Result<Option<gix::ObjectId>, Error> {
    let entries = read_tree(repo, tree_id)?;
    Ok(entries
        .into_iter()
        .find(|e| e.filename == name.as_bytes())
        .map(|e| e.oid))
}

/// Read a blob's raw bytes.
pub(crate) fn read_blob(repo: &gix::Repository, id: gix::ObjectId) -> Result<Vec<u8>, Error> {
    Ok(repo.find_blob(id).map_err(git_err)?.data.clone())
}

/// Resolve a sequence of path segments from `tree`, following named entries
/// only -- no decomposition, no fallback: a key not present at its derived
/// path was simply never written. Returns the final segment's object id, or
/// `None` the moment any segment along the way is missing.
pub(crate) fn resolve_at_path(
    repo: &gix::Repository,
    tree: gix::ObjectId,
    segments: &[String],
) -> Result<Option<gix::ObjectId>, Error> {
    let mut current = tree;
    for seg in segments {
        match find_entry(repo, current, seg)? {
            Some(id) => current = id,
            None => return Ok(None),
        }
    }
    Ok(Some(current))
}

/// A cheap "does this object still exist" check (a header lookup, not a
/// full read) — SG23's post-write presence verification.
pub(crate) fn object_exists(repo: &gix::Repository, id: gix::ObjectId) -> bool {
    use gix::objs::Exists as _;
    repo.objects.exists(&id)
}

#[cfg(test)]
mod tests {
    //! SG22/SG23, exercised directly against this module's own write path
    //! (white-box: `write_object` is private) rather than only against raw
    //! `gix`, which the architect seat's own probe (`gix-probes.md`, GP2)
    //! already covers.

    use super::*;

    fn init_repo() -> (tempfile::TempDir, gix::ThreadSafeRepository) {
        let dir = tempfile::tempdir().unwrap();
        let repo = gix::ThreadSafeRepository::init_opts(
            dir.path(),
            gix::create::Kind::Bare,
            gix::create::Options::default(),
            Default::default(),
        )
        .unwrap();
        (dir, repo)
    }

    fn loose_path(dir: &tempfile::TempDir, id: gix::ObjectId) -> std::path::PathBuf {
        let hex = id.to_hex().to_string();
        dir.path().join("objects").join(&hex[..2]).join(&hex[2..])
    }

    /// SG22: `write_object` writes through `write_buf_with_known_id` even
    /// when the object already exists, refreshing its mtime -- the same
    /// property GP2 confirmed for raw `gix`, now confirmed for this
    /// module's own call.
    #[test]
    fn write_object_refreshes_an_existing_objects_mtime() {
        let (dir, repo) = init_repo();
        let local = repo.to_thread_local();
        let bytes = b"sg22 probe payload";

        let id1 = write_blob(&local, bytes).unwrap();
        let path = loose_path(&dir, id1);
        assert!(path.is_file());

        let long_ago = std::time::SystemTime::now() - std::time::Duration::from_secs(3600);
        std::fs::File::open(&path)
            .unwrap()
            .set_modified(long_ago)
            .unwrap();
        let mtime_before = std::fs::metadata(&path).unwrap().modified().unwrap();
        assert_eq!(mtime_before, long_ago);

        let id2 = write_blob(&local, bytes).unwrap();
        assert_eq!(id1, id2);
        let mtime_after = std::fs::metadata(&path).unwrap().modified().unwrap();
        assert!(
            mtime_after > mtime_before,
            "write_object must refresh an existing object's mtime, not skip the write \
             (before={mtime_before:?}, after={mtime_after:?})"
        );
    }

    /// SG23: a subsequent call over the same content heals a gap left by a
    /// simulated concurrent deletion. This does not reach inside the single
    /// `write_object` call to race its own internal exists-check (no seam
    /// exists to inject that without a fake ODB); it demonstrates the
    /// operationally relevant property instead -- the object this layer
    /// depends on is never permanently lost, because the next write of the
    /// same content re-creates and re-verifies it.
    #[test]
    fn a_later_write_heals_a_simulated_missing_object() {
        let (dir, repo) = init_repo();
        let local = repo.to_thread_local();
        let bytes = b"sg23 probe payload";

        let id1 = write_blob(&local, bytes).unwrap();
        let path = loose_path(&dir, id1);
        assert!(path.is_file());
        std::fs::remove_file(&path).unwrap();
        assert!(!path.is_file(), "simulated concurrent prune");

        let id2 = write_blob(&local, bytes).unwrap();
        assert_eq!(id1, id2);
        assert!(
            path.is_file(),
            "a later write of the same content must heal the gap"
        );
    }
}
