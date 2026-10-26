//! Low-level `gix` plumbing: computing an object id under the repository's
//! own hash format and writing through the object database handle's
//! non-shortcut writer (SG22), syncing what was written to disk (SG31),
//! plus the small set of read helpers the key-derived path resolution needs.

use std::collections::BTreeSet;
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
    unsynced: &mut Unsynced,
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
    unsynced.object(repo, oid);
    Ok(oid)
}

/// Write a blob (SG22 write path).
pub(crate) fn write_blob(
    repo: &gix::Repository,
    unsynced: &mut Unsynced,
    data: &[u8],
) -> Result<gix::ObjectId, Error> {
    write_object(repo, unsynced, Kind::Blob, data)
}

/// The loose object files one `apply` wrote, and the directories whose
/// entries name them, not yet synced to disk (SG31). `gix` renames each
/// object's tempfile into place and never syncs it, nor the directory
/// holding the new name, so until [`Self::sync`] runs a power loss can drop
/// either.
#[derive(Default)]
pub(crate) struct Unsynced {
    files: BTreeSet<PathBuf>,
    dirs: BTreeSet<PathBuf>,
}

impl Unsynced {
    /// Record `id`'s loose file, its fan-out directory, and the objects
    /// directory (which names a fan-out directory `gix` may have just
    /// created). The path is the one `gix-odb`'s dynamic store writes to:
    /// the first loose database, which is the repository's own objects
    /// directory (`gix-odb` 0.84.0 `store_impls/dynamic/write.rs`).
    fn object(&mut self, repo: &gix::Repository, id: gix::ObjectId) {
        let objects = repo.objects.store_ref().path();
        let hex = id.to_hex().to_string();
        let fanout = objects.join(&hex[..2]);
        self.files.insert(fanout.join(&hex[2..]));
        self.dirs.insert(fanout);
        self.dirs.insert(objects.to_path_buf());
    }

    /// Sync every recorded file, then every recorded directory.
    pub(crate) fn sync(self) -> Result<(), Error> {
        for path in self.files.iter().chain(&self.dirs) {
            sync_path(path)?;
        }
        Ok(())
    }
}

/// Sync the loose ref file at `path` and every directory from its parent up
/// to and including `base`, any of which the ref update may have created
/// (SG31).
pub(crate) fn sync_ref(path: &Path, base: &Path) -> Result<(), Error> {
    sync_path(path)?;
    for dir in path.ancestors().skip(1) {
        sync_path(dir)?;
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

/// `fsync` one file or directory. A directory is synced by opening it, which
/// is how Linux exposes durability of the names a directory holds.
fn sync_path(path: &Path) -> Result<(), Error> {
    #[cfg(test)]
    SYNCED.with(|s| s.borrow_mut().push(path.to_path_buf()));
    std::fs::File::open(path)
        .and_then(|f| f.sync_all())
        .map_err(|e| Error::Sync(format!("fsync {}: {e}", path.display())))
}

/// One decoded tree entry, detached from the source tree's borrow.
#[derive(Debug, Clone)]
pub(crate) struct DecodedEntry {
    pub filename: BString,
    pub oid: gix::ObjectId,
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
        })
        .collect())
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

        let id1 = write_blob(&local, &mut Unsynced::default(), bytes).unwrap();
        let path = loose_path(&dir, id1);
        assert!(path.is_file());

        let long_ago = std::time::SystemTime::now() - std::time::Duration::from_secs(3600);
        std::fs::File::open(&path)
            .unwrap()
            .set_modified(long_ago)
            .unwrap();
        let mtime_before = std::fs::metadata(&path).unwrap().modified().unwrap();
        assert_eq!(mtime_before, long_ago);

        let id2 = write_blob(&local, &mut Unsynced::default(), bytes).unwrap();
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

        let id1 = write_blob(&local, &mut Unsynced::default(), bytes).unwrap();
        let path = loose_path(&dir, id1);
        assert!(path.is_file());
        std::fs::remove_file(&path).unwrap();
        assert!(!path.is_file(), "simulated concurrent prune");

        let id2 = write_blob(&local, &mut Unsynced::default(), bytes).unwrap();
        assert_eq!(id1, id2);
        assert!(
            path.is_file(),
            "a later write of the same content must heal the gap"
        );
    }
}
