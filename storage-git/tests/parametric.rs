//! Algorithm- and object-hash-format-parametricity tests: SG26, SG27.
//!
//! `src/layout.rs`'s source carries no reference to a specific hash
//! function or library (`grep -i 'sha\|blake\|md5'` over `src/` -- excluding
//! doc comments that merely name digest widths in prose -- returns no hits
//! outside this crate's tests, where two different `Hasher` widths are
//! deliberately exercised); this test is the runtime half of SG26/SG27:
//! the same differential scenario run over every combination of digest
//! width and git object-hash format.

mod common;

use common::{NarrowHasher, WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{Hasher, MemoryStorage, NaryMerkleLog, Storage, TreeConfig};
use storage_git::GitStorage;

async fn run<H: Hasher + Clone + 'static>(hasher: H, hash_kind: HashKind, arity: u64) {
    let (_dir, repo) = init_repo(hash_kind);
    assert_eq!(repo.to_thread_local().object_hash(), hash_kind, "repo must actually use the requested format");

    let git_storage = GitStorage::new(repo, "refs/eml/storage/param/staging", arity).unwrap();
    let mut git_log = NaryMerkleLog::new(git_storage, Box::new(hasher.clone()), TreeConfig { arity })
        .await
        .unwrap();
    let mut mem_log = NaryMerkleLog::new(MemoryStorage::new(), Box::new(hasher.clone()), TreeConfig { arity })
        .await
        .unwrap();

    for i in 0u8..23 {
        git_log.append_leaf(&[i, i, i]).await.unwrap();
        mem_log.append_leaf(&[i, i, i]).await.unwrap();
    }
    git_log.add_algorithm(1, Box::new(hasher.clone())).await.unwrap();
    mem_log.add_algorithm(1, Box::new(hasher.clone())).await.unwrap();
    for i in 23u8..31 {
        git_log.append_leaf(&[i, i, i]).await.unwrap();
        mem_log.append_leaf(&[i, i, i]).await.unwrap();
    }

    assert_eq!(git_log.size(), mem_log.size());
    for alg_id in [0u64, 1] {
        assert_eq!(git_log.root_for(alg_id).unwrap(), mem_log.root_for(alg_id).unwrap());
    }
    for i in 0..git_log.size() {
        assert_eq!(
            git_log.storage().get_leaf(i).await.unwrap(),
            mem_log.storage().get_leaf(i).await.unwrap()
        );
    }
    // A digest actually observed must be exactly this hasher's declared
    // width (SG15's converse: never a width this crate assumed).
    let one_node = git_log.storage().get_node(0, 0, 0).await.unwrap().unwrap();
    assert_eq!(one_node.len(), hasher.digest_len());
}

#[test]
fn narrow_hasher_over_sha1_repository() {
    smol::block_on(run(NarrowHasher, HashKind::Sha1, 2));
}

#[test]
fn wide_hasher_over_sha256_repository() {
    smol::block_on(run(WideHasher, HashKind::Sha256, 2));
}

#[test]
fn narrow_hasher_over_sha256_repository() {
    smol::block_on(run(NarrowHasher, HashKind::Sha256, 3));
}

#[test]
fn wide_hasher_over_sha1_repository() {
    smol::block_on(run(WideHasher, HashKind::Sha1, 3));
}
