//! Structural and golden-vector tests: SG1, SG4, SG5, SG6, SG9, SG12, SG16.

mod common;

use common::{WideHasher, init_repo};
use gix::hash::Kind as HashKind;
use gix::objs::tree::EntryKind;
use polydigest::{NaryMerkleLog, TreeConfig};
use storage_git::GitStorage;

fn read_entries(
    repo: &gix::Repository,
    id: gix::ObjectId,
) -> Vec<(String, gix::ObjectId, EntryKind)> {
    let tree = repo.find_tree(id).unwrap();
    let decoded = tree.decode().unwrap();
    decoded
        .entries
        .iter()
        .map(|e| (e.filename.to_string(), e.oid.to_owned(), e.mode.kind()))
        .collect()
}

fn checkpoint_tree(repo: &gix::ThreadSafeRepository, staging_ref: &str) -> gix::ObjectId {
    let local = repo.to_thread_local();
    let r = local.find_reference(staging_ref).unwrap();
    r.target().id().to_owned()
}

// SG1 ("C(n) is a tree with exactly the four top-level entries, present
// even at n = 0") used to be checked here two ways: via `tree_at(0)`'s
// synthetic pre-write construction (no ref exists yet at true genesis --
// `GitStorage` creates the ref lazily on the first write, so there is
// nothing durable for `n = 0` to mean before one), and via a real tree
// after the first append. `tree_at` is deleted outright by the head's
// 2026-09-16 design ruling, and the synthetic pre-write case it checked
// was never a state any checkpoint layer could actually observe. The
// durable half of this guarantee -- C(n) carries exactly these four
// entries from the very first real write onward -- is already covered,
// more thoroughly (five appends, not one), by
// `acceptance_layout.rs::sg1_checkpoint_tree_has_exactly_four_top_level_entries`.

/// SG4/SG10: a flat append materializes `T(left,0)` with `leaf` + `digest/`;
/// a subtree append leaves it opaque (`digest/` only, no `leaf`).
#[test]
fn sg4_sg10_materialized_vs_opaque_leaf_node() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/t/staging";
        let storage = GitStorage::new(repo.clone(), staging, 2).unwrap();
        let mut log = NaryMerkleLog::new(storage, Box::new(WideHasher), TreeConfig { arity: 2 })
            .await
            .unwrap();
        log.append_leaf(b"flat-leaf").await.unwrap();
        let _ = log.into_storage();

        let local = repo.to_thread_local();
        let tree = checkpoint_tree(&repo, staging);

        // Descend peaks/00/00 -> the lone height-0 peak for item 0.
        let peaks_id = find(&local, tree, "peaks");
        let group_id = find(&local, peaks_id, "00");
        let node_id = find(&local, group_id, "00");
        let entries = read_entries(&local, node_id);
        let names: Vec<&str> = entries.iter().map(|(n, ..)| n.as_str()).collect();
        assert!(
            names.contains(&"leaf"),
            "materialized leaf node must carry `leaf`"
        );
        assert!(names.contains(&"digest"), "every node carries `digest/`");
        let leaf_id = find(&local, node_id, "leaf");
        assert_eq!(local.find_blob(leaf_id).unwrap().data, b"flat-leaf");
    });

    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/t2/staging";
        let storage = GitStorage::new(repo.clone(), staging, 2).unwrap();
        let mut log = NaryMerkleLog::new(storage, Box::new(WideHasher), TreeConfig { arity: 2 })
            .await
            .unwrap();
        log.append_subtree(&spine::Subtree::Leaf(b"opaque".to_vec()))
            .await
            .unwrap();
        let _ = log.into_storage();

        let local = repo.to_thread_local();
        let tree = checkpoint_tree(&repo, staging);
        let peaks_id = find(&local, tree, "peaks");
        let group_id = find(&local, peaks_id, "00");
        let node_id = find(&local, group_id, "00");
        let entries = read_entries(&local, node_id);
        let names: Vec<&str> = entries.iter().map(|(n, ..)| n.as_str()).collect();
        assert!(
            !names.contains(&"leaf"),
            "opaque node must not carry `leaf`"
        );
        assert_eq!(
            names,
            vec!["digest"],
            "opaque node carries digest/ only (SG4)"
        );
    });
}

/// SG5: every blob entry uses mode `100644`; every tree entry uses `40000`.
#[test]
fn sg5_entry_modes() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/t/staging";
        let storage = GitStorage::new(repo.clone(), staging, 2).unwrap();
        let mut log = NaryMerkleLog::new(storage, Box::new(WideHasher), TreeConfig { arity: 2 })
            .await
            .unwrap();
        log.append_leaf(b"x").await.unwrap();
        let _ = log.into_storage();

        let local = repo.to_thread_local();
        let tree = checkpoint_tree(&repo, staging);
        for (name, _, kind) in read_entries(&local, tree) {
            match name.as_str() {
                "meta" => assert_eq!(kind, EntryKind::Blob),
                "epochs" | "roots" | "peaks" => assert_eq!(kind, EntryKind::Tree),
                other => panic!("unexpected top-level entry {other}"),
            }
        }
        let peaks_id = find(&local, tree, "peaks");
        let group_id = find(&local, peaks_id, "00");
        let node_id = find(&local, group_id, "00");
        for (name, _, kind) in read_entries(&local, node_id) {
            match name.as_str() {
                "leaf" => assert_eq!(kind, EntryKind::Blob),
                "digest" => assert_eq!(kind, EntryKind::Tree),
                other => panic!("unexpected node entry {other}"),
            }
        }
        let digest_id = find(&local, node_id, "digest");
        for (_, _, kind) in read_entries(&local, digest_id) {
            assert_eq!(kind, EntryKind::Blob);
        }
    });
}

/// SG12/SG16: `meta` is exactly 11 bytes in the documented layout, and
/// `leaf` is byte-identical to what `store_leaf` received.
#[test]
fn sg12_sg16_golden_bytes() {
    smol::block_on(async {
        let (_dir, repo) = init_repo(HashKind::Sha1);
        let staging = "refs/eml/storage/t/staging";
        let storage = GitStorage::new(repo.clone(), staging, 3).unwrap();
        let mut log = NaryMerkleLog::new(storage, Box::new(WideHasher), TreeConfig { arity: 3 })
            .await
            .unwrap();
        log.append_leaf(b"hello world, byte for byte")
            .await
            .unwrap();
        let _ = log.into_storage();

        let local = repo.to_thread_local();
        let tree = checkpoint_tree(&repo, staging);
        let meta_id = find(&local, tree, "meta");
        let meta_bytes = local.find_blob(meta_id).unwrap().data.clone();
        assert_eq!(meta_bytes.len(), 11);
        assert_eq!(
            u16::from_be_bytes([meta_bytes[0], meta_bytes[1]]),
            3,
            "arity"
        );
        assert_eq!(
            u64::from_be_bytes(meta_bytes[2..10].try_into().unwrap()),
            1,
            "count"
        );
        assert_eq!(meta_bytes[10], 0, "kind byte: Flat");

        let peaks_id = find(&local, tree, "peaks");
        let group_id = find(&local, peaks_id, "00");
        let node_id = find(&local, group_id, "00");
        let leaf_id = find(&local, node_id, "leaf");
        assert_eq!(
            local.find_blob(leaf_id).unwrap().data,
            b"hello world, byte for byte"
        );
    });
}

/// SG9: `C(n)`'s object id does not depend on insertion order among
/// operations that reach the same logical state -- here, two algorithm
/// registrations at the same size, in either order.
#[test]
fn sg9_purity_under_reordering() {
    smol::block_on(async {
        let (_dir, repo_a) = init_repo(HashKind::Sha1);
        let staging_a = "refs/eml/storage/a/staging";
        let storage_a = GitStorage::new(repo_a.clone(), staging_a, 2).unwrap();
        let mut log_a =
            NaryMerkleLog::new(storage_a, Box::new(WideHasher), TreeConfig { arity: 2 })
                .await
                .unwrap();
        log_a.add_algorithm(7, Box::new(WideHasher)).await.unwrap();
        log_a.add_algorithm(9, Box::new(WideHasher)).await.unwrap();
        log_a.append_leaf(b"x").await.unwrap();
        let _ = log_a.into_storage();

        let (_dir, repo_b) = init_repo(HashKind::Sha1);
        let staging_b = "refs/eml/storage/b/staging";
        let storage_b = GitStorage::new(repo_b.clone(), staging_b, 2).unwrap();
        let mut log_b =
            NaryMerkleLog::new(storage_b, Box::new(WideHasher), TreeConfig { arity: 2 })
                .await
                .unwrap();
        // Same two algorithms, reversed registration order.
        log_b.add_algorithm(9, Box::new(WideHasher)).await.unwrap();
        log_b.add_algorithm(7, Box::new(WideHasher)).await.unwrap();
        log_b.append_leaf(b"x").await.unwrap();
        let _ = log_b.into_storage();

        let tree_a = checkpoint_tree(&repo_a, staging_a);
        let tree_b = checkpoint_tree(&repo_b, staging_b);
        assert_eq!(
            tree_a, tree_b,
            "reordered-but-equivalent state must yield identical C(n)"
        );
    });
}

fn find(repo: &gix::Repository, tree: gix::ObjectId, name: &str) -> gix::ObjectId {
    repo.find_entry_id(tree, name)
        .unwrap_or_else(|| panic!("missing entry {name} in tree {tree}"))
}

/// Small helper extension so tests can name entries directly, mirroring
/// `storage_git`'s own internal `find_entry` (kept private to the crate).
trait FindEntryId {
    fn find_entry_id(&self, tree: gix::ObjectId, name: &str) -> Option<gix::ObjectId>;
}

impl FindEntryId for gix::Repository {
    fn find_entry_id(&self, tree: gix::ObjectId, name: &str) -> Option<gix::ObjectId> {
        let decoded = self.find_tree(tree).ok()?;
        let entries = decoded.decode().ok()?;
        entries
            .entries
            .iter()
            .find(|e| e.filename == name.as_bytes())
            .map(|e| e.oid.to_owned())
    }
}
