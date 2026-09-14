//! Acceptance tests for §2.6's materialized-vs-opaque distinction:
//! SG10 (a subtree-kind or resumed node MUST be opaque) and SG11 (opacity is
//! a property of the node's own provenance, never inferred from the log's
//! `meta.kind` byte), from `docs/specs/storage-git.md` alone.

#[path = "acceptance_support/mod.rs"]
mod support;

use polydigest::NaryMerkleLog;
use spine::Subtree;
use support::{FixtureHasher, bare_repo, hex, new_log};

/// [SG10] A `T(left, 0)` node built from `Storage::store_node` with no
/// corresponding `store_leaf` call -- exactly what happens for every
/// subtree-kind append -- MUST be opaque: `digest/` only, no `leaf`.
#[test]
fn sg10_subtree_kind_append_is_opaque() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg10-subtree/staging";
        // High arity: every append stays an isolated height-0 peak, so its
        // ordinal under peaks/00/ is just its index.
        let mut log = new_log(&repo, staging, 50, FixtureHasher::new(32)).await;

        for i in 0..3u32 {
            log.append_subtree(&Subtree::Leaf(format!("subtree-leaf-{i}").into_bytes()))
                .await
                .unwrap();
        }

        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, staging).unwrap();
        for i in 0..3u64 {
            let path = format!("peaks/{}/{}", hex(0, 2), hex(i, 2));
            let node = support::resolve_path(&local, tip, &path)
                .unwrap_or_else(|| panic!("no peak at {path}"))
                .oid;
            let entries = support::read_tree(&local, node);
            assert!(
                !entries.iter().any(|e| e.name == "leaf"),
                "T({i},0) built via append_subtree must not carry a materialized leaf blob"
            );
            assert!(
                entries.iter().any(|e| e.name == "digest"),
                "T({i},0) must still carry digest/"
            );
        }
    });
}

/// [SG10]/[SG11] A node inherited opaque from a resumed seal MUST be
/// opaque -- `digest/` only, no children -- even though it covers a
/// height > 0 range that, for a live flat log, would ordinarily be fully
/// materialized. This shows opacity tracks *how a specific node's write was
/// provisioned* (SG11), not `meta.kind`: the resumed write only ever
/// supplies a raw peak digest via `store_node`, never the children a
/// height > 0 materialized node would need, regardless of whether an
/// earlier, differently-provisioned object at a different git id happened
/// to materialize the same logical range.
#[test]
fn sg10_11_resumed_peak_is_opaque_despite_covering_a_once_materialized_range() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg11/staging";
        let k = 2u64;
        let hasher0 = FixtureHasher::new(32);

        // Build a flat, fully materialized log to n=4 (one peak, T(0,2)).
        let mut log = new_log(&repo, staging, k, hasher0.clone()).await;
        for i in 0..4u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }

        let local = repo.to_thread_local();
        let materialized_tip = support::ref_target(&local, staging).unwrap();
        let materialized_peak = support::resolve_path(
            &local,
            materialized_tip,
            &format!("peaks/{}/{}", hex(2, 2), hex(0, 2)),
        )
        .unwrap()
        .oid;
        assert!(
            support::read_tree(&local, materialized_peak)
                .iter()
                .any(|e| e.name == hex(0, 2)),
            "sanity: the pre-resumption peak T(0,2) must start out materialized (SG4)"
        );

        // Seal, then resume -- onto the *same* GitStorage/ref this log was
        // already writing to, so the object database it resumes into is the
        // one that already holds the materialized objects above.
        let sealed = log.seal().await.unwrap();
        let resumed_storage = support_reopen(&repo, staging, k);
        let mut resumed: NaryMerkleLog<storage_git::GitStorage> = NaryMerkleLog::resume(
            &sealed,
            resumed_storage,
            vec![(0, Box::new(hasher0.clone()))],
        )
        .await
        .unwrap();

        let resumed_tip = support::ref_target(&local, staging).unwrap();
        let resumed_peak = support::resolve_path(
            &local,
            resumed_tip,
            &format!("peaks/{}/{}", hex(2, 2), hex(0, 2)),
        )
        .unwrap()
        .oid;
        assert_ne!(
            resumed_peak, materialized_peak,
            "the resumed T(0,2) reused the exact same (materialized) git tree object id as the \
             pre-resumption peak, instead of a fresh digest-only object"
        );

        let entries = support::read_tree(&local, resumed_peak);
        assert!(
            !entries.iter().any(|e| e.name == hex(0, 2))
                && !entries.iter().any(|e| e.name == hex(1, 2)),
            "T(0,2) resumed from a seal must be opaque: no hex(c,2) children, even though the \
             same coordinate was materialized moments ago under the pre-resumption log"
        );
        assert!(
            !entries.iter().any(|e| e.name == "leaf"),
            "T(0,2) resumed from a seal must carry no leaf"
        );
        assert!(
            entries.iter().any(|e| e.name == "digest"),
            "T(0,2) resumed from a seal must still carry digest/"
        );

        // Forward appends on a resumed (Subtree-kind) log go through
        // append_subtree and must themselves be opaque too (SG10 again, on
        // the same instance that just inherited an opaque peak -- SG11's
        // "single log instance" carrying opaque nodes from a single,
        // consistent provenance class after resumption).
        resumed
            .append_subtree(&Subtree::Leaf(b"forward-1".to_vec()))
            .await
            .unwrap();
        let after_forward_tip = support::ref_target(&local, staging).unwrap();
        let forward_leaf_path = format!("peaks/{}/{}", hex(0, 2), hex(0, 2));
        let forward_node = support::resolve_path(&local, after_forward_tip, &forward_leaf_path)
            .unwrap_or_else(|| panic!("no peak at {forward_leaf_path}"))
            .oid;
        let forward_entries = support::read_tree(&local, forward_node);
        assert!(
            !forward_entries.iter().any(|e| e.name == "leaf"),
            "a forward subtree append on a resumed log must be opaque too"
        );
    });
}

/// Reopen a fresh `GitStorage` handle over the same on-disk repository and
/// ref, for use as `resume`'s "fresh backend the resumed log writes forward
/// into" -- deliberately the *same* physical object database and ref name
/// the pre-resumption log used, so a reader inspecting `staging` afterwards
/// observes the resumed state directly.
fn support_reopen(
    repo: &gix::ThreadSafeRepository,
    staging: &str,
    arity: u64,
) -> storage_git::GitStorage {
    storage_git::GitStorage::new(repo.clone(), staging, arity)
        .expect("reopen GitStorage for resume")
}
