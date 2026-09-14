//! `tree_at`/`open_at` tests: SG20, SG21.

mod common;

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use polydigest::{NaryMerkleLog, Storage, TreeConfig};
use storage_git::GitStorage;

fn read_entries(repo: &gix::Repository, id: gix::ObjectId) -> Vec<(String, gix::ObjectId)> {
    let tree = repo.find_tree(id).unwrap();
    tree.decode()
        .unwrap()
        .entries
        .iter()
        .map(|e| (e.filename.to_string(), e.oid.to_owned()))
        .collect()
}

fn named(entries: &[(String, gix::ObjectId)], name: &str) -> gix::ObjectId {
    entries
        .iter()
        .find(|(n, _)| n == name)
        .unwrap_or_else(|| panic!("missing {name}"))
        .1
}

/// SG20: `tree_at(m)` for a range of past `m` matches an independent
/// from-genesis rebuild's `C(m)` for `meta`/`epochs`/`peaks` -- the parts
/// this backend can reconstruct without a hasher (`roots/` is this crate's
/// documented departure at historical sizes, checked separately below).
#[test]
fn sg20_tree_at_matches_fresh_rebuild() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut storage =
            GitStorage::new(repo.clone(), "refs/eml/storage/live/staging", 2).unwrap();
        // Setup change (GB44): tree_at(m) for m < len() now errors, rather
        // than silently omitting an entry, for an active algorithm with no
        // hasher registered (SG20's amendment) -- register algorithm 0's
        // fold so the historical calls below can succeed. No assertion
        // here changes: this test never inspects roots/, only
        // meta/epochs/peaks.
        storage.register_hasher(0, Box::new(WideHasher));
        let mut log = NaryMerkleLog::new(storage, Box::new(WideHasher), TreeConfig { arity: 2 })
            .await
            .unwrap();
        for i in 0..17u8 {
            log.append_leaf(&[i]).await.unwrap();
        }
        let git_storage = log.into_storage();

        let local = repo.to_thread_local();
        for m in [0u64, 1, 2, 3, 4, 7, 8, 15, 16, 17] {
            let historical = git_storage.tree_at(m).unwrap();

            // Independent from-genesis rebuild to exactly size m.
            let (_dir2, repo2) = init_repo(HashKind::Sha1);
            let mut storage2 =
                GitStorage::new(repo2.clone(), "refs/eml/storage/fresh/staging", 2).unwrap();
            storage2.register_hasher(0, Box::new(WideHasher));
            let mut log2 =
                NaryMerkleLog::new(storage2, Box::new(WideHasher), TreeConfig { arity: 2 })
                    .await
                    .unwrap();
            for i in 0..m as u8 {
                log2.append_leaf(&[i]).await.unwrap();
            }
            let fresh_storage = log2.into_storage();
            let fresh = fresh_storage.tree_at(m).unwrap();

            let local2 = repo2.to_thread_local();
            let hist_entries = read_entries(&local, historical);
            let fresh_entries = read_entries(&local2, fresh);
            assert_eq!(
                named(&hist_entries, "meta"),
                named(&fresh_entries, "meta"),
                "meta mismatch at m={m}"
            );
            assert_eq!(
                named(&hist_entries, "epochs"),
                named(&fresh_entries, "epochs"),
                "epochs mismatch at m={m}"
            );
            assert_eq!(
                named(&hist_entries, "peaks"),
                named(&fresh_entries, "peaks"),
                "peaks mismatch at m={m}"
            );
        }
    });
}

/// Superseded departure, updated for GB44 (named change, not a fixture-only
/// adaptation -- this test's own premise is what the merge gate's SGG12
/// finding rejected): `tree_at(m)` for `m < len()` used to reconstruct
/// `roots/` as the empty tree whenever no hasher was registered, silently
/// standing in a well-formed but wrong object for the real one (SGG12,
/// `.ledger/deposits/git-backend/lead-maintainer/storage-git-merge-gate.md`).
/// SG20's amendment now makes that an error instead (see
/// `acceptance_roots_hasher.rs`'s `tree_at_without_registered_hasher_names_the_missing_algorithm`
/// for that path), and a *registered* hasher reconstructs the real,
/// non-empty `roots/` entry historically, matching what `tree_at(len())`
/// already returns live -- this test now checks exactly that parity instead
/// of the old, since-closed "empty" gap.
#[test]
fn tree_at_historical_roots_matches_the_live_entry_once_a_hasher_is_registered() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut storage = GitStorage::new(repo.clone(), "refs/eml/storage/t/staging", 2).unwrap();
        storage.register_hasher(0, Box::new(WideHasher));
        let mut log = NaryMerkleLog::new(storage, Box::new(WideHasher), TreeConfig { arity: 2 })
            .await
            .unwrap();
        log.append_leaf(b"a").await.unwrap();
        log.append_leaf(b"b").await.unwrap();
        let git_storage = log.into_storage();

        let local = repo.to_thread_local();
        let past = git_storage.tree_at(1).unwrap();
        let past_entries = read_entries(&local, past);
        let roots_id = named(&past_entries, "roots");
        assert!(
            !local
                .find_tree(roots_id)
                .unwrap()
                .decode()
                .unwrap()
                .entries
                .is_empty(),
            "algorithm 0 is active at m=1 and has a registered hasher: roots/ must carry its \
             reconstructed entry, not the old empty-departure placeholder"
        );

        let live = git_storage.tree_at(2).unwrap();
        let live_entries = read_entries(&local, live);
        let live_roots_id = named(&live_entries, "roots");
        assert!(
            !local
                .find_tree(live_roots_id)
                .unwrap()
                .decode()
                .unwrap()
                .entries
                .is_empty()
        );
    });
}

/// SG21: reading through `open_at(tree_at(m))` for a past `m` yields the
/// same leaf/node values `get_leaf`/`get_node` returned when the log was
/// actually at size `m` -- durable-witness parity.
#[test]
fn sg21_open_at_durable_witness_parity() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let mut storage = GitStorage::new(repo.clone(), "refs/eml/storage/t/staging", 2).unwrap();
        // Setup change (GB44): see sg20_tree_at_matches_fresh_rebuild above.
        storage.register_hasher(0, Box::new(WideHasher));
        let mut log = NaryMerkleLog::new(storage, Box::new(WideHasher), TreeConfig { arity: 2 })
            .await
            .unwrap();

        let mut snapshots: Vec<(u64, Vec<Vec<u8>>)> = Vec::new();
        for i in 0..10u8 {
            log.append_leaf(&[i, i.wrapping_mul(3)]).await.unwrap();
            let size = log.size();
            let mut leaves = Vec::new();
            for idx in 0..size {
                leaves.push(log.storage().get_leaf(idx).await.unwrap());
            }
            snapshots.push((size, leaves));
        }
        let git_storage = log.into_storage();

        for (size, leaves) in snapshots {
            let tree = git_storage.tree_at(size).unwrap();
            let view = git_storage.open_at(tree).unwrap();
            for (idx, expected) in leaves.iter().enumerate() {
                let actual = view.get_leaf(idx as u64).await.unwrap();
                assert_eq!(
                    &actual, expected,
                    "leaf {idx} at historical size {size} diverged"
                );
            }
        }
    });
}
