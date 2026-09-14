//! GC-safety, end to end through the public `Storage` API: SG22.
//!
//! `src/gitutil.rs`'s own unit tests already exercise SG22/SG23 directly
//! against this crate's write primitive (white-box, since it is private);
//! this test confirms the same property holds through a real
//! `write_batch` call a caller would actually make.

mod common;

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{NaryMerkleLog, TreeConfig};
use storage_git::GitStorage;

/// An algorithm's `epochs/hex(alg_id,16)` blob is byte-identical across two
/// appends that don't touch that algorithm's epoch history (proved in this
/// crate's design notes: `AlgView::epochs_at` is invariant under a growing
/// size as long as the underlying epoch list is unchanged) -- so the second
/// append's `write_batch` call writes the *same* object id again. That
/// write must still go through (not be skipped because the object already
/// exists), refreshing its mtime.
#[test]
fn write_batch_refreshes_an_unchanged_epochs_blob() {
    smol::block_on(async {
        let (dir, repo) = init_repo(HashKind::Sha1);
        let storage = GitStorage::new(repo.clone(), "refs/eml/storage/gc/staging", 2).unwrap();
        let mut log = NaryMerkleLog::new(storage, Box::new(WideHasher), TreeConfig { arity: 2 })
            .await
            .unwrap();
        log.append_leaf(b"one").await.unwrap();

        let local = repo.to_thread_local();
        let tree = local
            .find_reference("refs/eml/storage/gc/staging")
            .unwrap()
            .target()
            .id()
            .to_owned();
        let epochs_group = find(&local, tree, "epochs");
        let epochs_blob = find(&local, epochs_group, &storage_git_hex16(0));
        let path = loose_path(dir.path(), epochs_blob);
        assert!(path.is_file());

        let long_ago = std::time::SystemTime::now() - std::time::Duration::from_secs(3600);
        std::fs::File::open(&path)
            .unwrap()
            .set_modified(long_ago)
            .unwrap();
        let mtime_before = std::fs::metadata(&path).unwrap().modified().unwrap();
        assert_eq!(mtime_before, long_ago);

        log.append_leaf(b"two").await.unwrap();

        let tree2 = local
            .find_reference("refs/eml/storage/gc/staging")
            .unwrap()
            .target()
            .id()
            .to_owned();
        let epochs_group2 = find(&local, tree2, "epochs");
        let epochs_blob2 = find(&local, epochs_group2, &storage_git_hex16(0));
        assert_eq!(
            epochs_blob, epochs_blob2,
            "epochs blob content must be unchanged"
        );

        let mtime_after = std::fs::metadata(&path).unwrap().modified().unwrap();
        assert!(
            mtime_after > mtime_before,
            "an unchanged-but-rereferenced object must still be freshened on write (SG22)"
        );
    });
}

fn find(repo: &gix::Repository, tree: gix::ObjectId, name: &str) -> gix::ObjectId {
    let decoded = repo.find_tree(tree).unwrap();
    decoded
        .decode()
        .unwrap()
        .entries
        .iter()
        .find(|e| e.filename == name.as_bytes())
        .unwrap_or_else(|| panic!("missing {name}"))
        .oid
        .to_owned()
}

fn loose_path(root: &std::path::Path, id: gix::ObjectId) -> std::path::PathBuf {
    let hex = id.to_hex().to_string();
    root.join("objects").join(&hex[..2]).join(&hex[2..])
}

fn storage_git_hex16(x: u64) -> String {
    format!("{x:016x}")
}
