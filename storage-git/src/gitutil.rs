//! Low-level `gix` plumbing: computing an object id under the repository's
//! own hash format and writing through the object database handle's
//! non-shortcut writer (SG22), plus the small set of read helpers the
//! position-lookup and tree-assembly code needs.

use gix::bstr::BString;
use gix::objs::tree::{Entry, EntryKind};
use gix::objs::{Kind, Tree, Write as _, WriteTo as _};

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

/// Build and write a tree object from `entries` (SG22 write path). Entries
/// are sorted by git's canonical tree order (SG7) unconditionally — `gix`
/// only `debug_assert!`s pre-sorted order and never sorts for us.
pub(crate) fn write_tree(
    repo: &gix::Repository,
    mut entries: Vec<Entry>,
) -> Result<gix::ObjectId, Error> {
    entries.sort();
    let tree = Tree { entries };
    let mut buf = Vec::new();
    tree.write_to(&mut buf).map_err(git_err)?;
    write_object(repo, Kind::Tree, &buf)
}

/// One decoded tree entry, detached from the source tree's borrow.
#[derive(Debug, Clone)]
pub(crate) struct DecodedEntry {
    pub filename: BString,
    pub oid: gix::ObjectId,
    pub kind: EntryKind,
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
            kind: e.mode.kind(),
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

/// A cheap "does this object still exist" check (a header lookup, not a
/// full read) — SG23's post-write presence verification.
pub(crate) fn object_exists(repo: &gix::Repository, id: gix::ObjectId) -> bool {
    use gix::objs::Exists as _;
    repo.objects.exists(&id)
}

pub(crate) fn entry(kind: EntryKind, name: impl Into<BString>, oid: gix::ObjectId) -> Entry {
    Entry {
        mode: kind.into(),
        filename: name.into(),
        oid,
    }
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

    /// SG7: `gix::objs::Tree::write_to` does not sort entries -- it only
    /// `debug_assert!`s pre-sorted order (compiled out in release), so
    /// `write_tree` must sort them itself in every profile. Confirmed two
    /// ways: every permutation of the same entry set produces the same
    /// (correctly sorted) object id through `write_tree`, and that id
    /// differs from the id a naive, unsorted serialization of the same
    /// entries would produce -- proving the sort is doing real work, not
    /// merely a no-op on already-sorted input.
    #[test]
    fn write_tree_sorts_entries_regardless_of_input_order() {
        let (_dir, repo) = init_repo();
        let local = repo.to_thread_local();

        let a = write_blob(&local, b"a").unwrap();
        let b = write_blob(&local, b"b").unwrap();
        let c = write_blob(&local, b"c").unwrap();
        let mk = |name: &str, oid: gix::ObjectId| entry(EntryKind::Blob, name, oid);

        // Deliberately unsorted (reverse of canonical order: "cc" > "bb" > "aa").
        let unsorted = vec![mk("cc", c), mk("aa", a), mk("bb", b)];
        let reversed = vec![mk("bb", b), mk("cc", c), mk("aa", a)];
        let already_sorted = vec![mk("aa", a), mk("bb", b), mk("cc", c)];

        let id_unsorted = write_tree(&local, unsorted.clone()).unwrap();
        let id_reversed = write_tree(&local, reversed).unwrap();
        let id_sorted = write_tree(&local, already_sorted).unwrap();
        assert_eq!(
            id_unsorted, id_sorted,
            "write_tree must sort regardless of input order"
        );
        assert_eq!(id_reversed, id_sorted);

        // A naive write that skips the sort either panics on gix's own
        // `debug_assert!` (this test runs with debug assertions on, like
        // any `cargo test`) or -- in a release build, where that assertion
        // compiles out -- would silently serialize the wrong bytes. Either
        // way, skipping `write_tree`'s own unconditional sort is never
        // safe; `catch_unwind` here demonstrates the debug-mode half of
        // that claim without taking down the whole test binary.
        let naive = std::panic::catch_unwind(|| {
            let mut naive_buf = Vec::new();
            Tree { entries: unsorted }.write_to(&mut naive_buf).unwrap();
            naive_buf
        });
        match naive {
            Err(_) => {}, /* gix's debug_assert! caught it first -- expected under debug */
            // assertions.
            Ok(naive_buf) => {
                let naive_id = write_object(&local, Kind::Tree, &naive_buf).unwrap();
                assert_ne!(
                    naive_id, id_sorted,
                    "the unsorted serialization must differ from the sorted one"
                );
            },
        }
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
