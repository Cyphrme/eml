//! [NO STORED KIND] Head's ruling, 2026-09-17, requirement A/(2): a log's
//! kind is derived from content, never persisted. `storage-git`'s `meta`
//! blob therefore carries exactly two fields -- arity (u16 BE) and append
//! count (u64 BE) -- 10 bytes, never 11: there is no kind byte and no
//! version byte (nothing this early in the format's life to stay compatible
//! with).
//!
//! Passing at HEAD: `layout::encode_meta`/`decode_meta` already produce/expect
//! the 10-byte, kind-free shape (`storage-git/src/layout.rs::encode_meta`
//! returns `[u8; 10]`, `decode_meta` rejects any other length). Checked at
//! the raw byte level, straight off the git tree -- independent of
//! `storage-git`'s own `decode_meta` (which is exactly the function under
//! scrutiny; asserting the byte LENGTH does not depend on trusting it to
//! decode correctly). Demonstrated by mutation: reverting `encode_meta` to
//! an 11-byte, kind-carrying shape turns this red immediately.

mod common;

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{NaryMerkleLog, TreeConfig};
use storage_git::GitStorage;

fn meta_len(repo: &gix::ThreadSafeRepository, staging: &str) -> usize {
    let local = repo.to_thread_local();
    let tip = local
        .try_find_reference(staging)
        .unwrap()
        .unwrap()
        .peel_to_id()
        .unwrap()
        .detach();
    let tree = local.find_tree(tip).unwrap();
    let decoded = tree.decode().unwrap();
    let meta_entry = decoded
        .entries
        .iter()
        .find(|e| e.filename == "meta".as_bytes())
        .expect("meta entry must exist");
    local
        .find_blob(meta_entry.oid.to_owned())
        .unwrap()
        .data
        .len()
}

/// [NO STORED KIND] `meta` is exactly 10 bytes after a genesis write (arity,
/// append count) -- demonstrated by mutation: reverting `layout::encode_meta`
/// to an 11-byte, kind-carrying shape turns this red.
#[test]
fn meta_blob_carries_no_kind_byte_at_genesis() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/no-stored-kind/genesis/staging";
        let _log = NaryMerkleLog::new(
            GitStorage::new(repo.clone(), staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();

        assert_eq!(
            meta_len(&repo, staging),
            10,
            "meta must be exactly 10 bytes (arity u16 + count u64), no kind byte and no version \
             byte"
        );
    });
}

/// [NO STORED KIND] `meta` stays 10 bytes across appends, algorithm
/// add/remove/resume, and a resume from a sealed frontier -- the shape
/// never grows a kind field back in for any lifecycle.
#[test]
fn meta_blob_carries_no_kind_byte_across_the_full_lifecycle() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/no-stored-kind/lifecycle/staging";
        let mut log = NaryMerkleLog::new(
            GitStorage::new(repo.clone(), staging, 2).unwrap(),
            Box::new(WideHasher),
            TreeConfig { arity: 2 },
        )
        .await
        .unwrap();

        log.append_leaf(b"one").await.unwrap();
        assert_eq!(meta_len(&repo, staging), 10);

        log.add_algorithm(1, Box::new(WideHasher)).await.unwrap();
        assert_eq!(meta_len(&repo, staging), 10);

        log.append_leaf(b"two").await.unwrap();
        log.remove_algorithm(1).await.unwrap();
        assert_eq!(meta_len(&repo, staging), 10);

        log.append_leaf(b"three").await.unwrap();
        log.resume_algorithm(1).await.unwrap();
        assert_eq!(meta_len(&repo, staging), 10);

        let sealed = log.seal().await.unwrap();
        let (_dir2, repo2) = init_repo(HashKind::Sha1);
        let staging2 = "refs/eml/storage/no-stored-kind/resumed/staging";
        let hashers: Vec<(u64, Box<dyn polydigest::Hasher>)> = sealed
            .frontiers()
            .iter()
            .map(|&(id, _)| (id, Box::new(WideHasher) as Box<dyn polydigest::Hasher>))
            .collect();
        let _resumed = NaryMerkleLog::resume(
            &sealed,
            GitStorage::new(repo2.clone(), staging2, 2).unwrap(),
            hashers,
        )
        .await
        .unwrap();
        assert_eq!(meta_len(&repo2, staging2), 10);
    });
}
