//! Acceptance tests for §3's byte-exact blob encodings, from
//! `docs/specs/storage-git.md` alone: SG12 (`meta`), SG13 (`epochs/`),
//! SG15 (node bytes verbatim), and SG16 (`leaf`). SG14 (`roots/`) is not
//! tested here: a `roots/` entry never exists at all now (head's ruling,
//! 2026-09-17, `storage-git/tests/acceptance_no_application_index.rs`),
//! which strictly subsumes the narrower present-iff-active claim SG14 used
//! to name.

#[path = "acceptance_support/mod.rs"]
mod support;

use cml::engine::AlgView;
use polydigest::NaryMerkleLog;
use storage_git::GitStorage;
use support::{FixtureHasher, bare_repo, hex, new_log};

/// [SG12] `meta` MUST be exactly 10 bytes: arity (u16 BE), count (u64 BE),
/// with no trailing padding and no version byte -- there is nothing this
/// early in the format's life to stay compatible with, so no discriminator
/// field exists to distinguish a shape that has never had a second variant.
/// No kind byte either: a log's kind is derived from content, never stored
/// (head's ruling, 2026-09-17) -- `tests/no_stored_kind.rs` is this crate's
/// pinned statement of that derivation; this test's own claim is narrower
/// and purely about width and slack, so it stops at the two fields meta
/// actually carries rather than re-asserting kind derivation here too.
#[test]
fn sg12_meta_blob_is_10_exact_bytes_with_no_version_byte_and_no_kind_byte() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg12/staging";
        let k = 5u64;
        let mut log = new_log(&repo, staging, k, FixtureHasher::new(32)).await;
        let local = repo.to_thread_local();

        for n in 0..7u32 {
            let tip = support::ref_target(&local, staging).unwrap();
            let meta_id = support::find_entry(&local, tip, "meta").unwrap().oid;
            let bytes = support::read_blob(&local, meta_id);
            assert_eq!(
                bytes.len(),
                10,
                "n={n}: meta must be exactly 10 bytes (arity + count, no version byte, no kind \
                 byte), got {}",
                bytes.len()
            );
            let arity = u16::from_be_bytes([bytes[0], bytes[1]]);
            assert_eq!(arity as u64, k, "n={n}: meta.arity must be {k}");
            let count = u64::from_be_bytes(bytes[2..10].try_into().unwrap());
            assert_eq!(count, n as u64, "n={n}: meta.count must be {n}");

            log.append_leaf(format!("leaf-{n}").as_bytes())
                .await
                .unwrap();
        }
    });
}

/// [SG13] The epoch list at `epochs/hex(alg_id,16)` inside `C(n)` MUST equal
/// `AlgView::epochs_at(n)` applied to the algorithm's full, currently-known
/// epoch history.
///
/// Rewritten to stop calling `tree_at` (deleted outright
/// per the head's 2026-09-16 design ruling): each checked size's tree is
/// now recorded straight off the staging ref at the exact moment its epoch
/// state stops changing -- right after `new_log`'s own genesis write (n=0),
/// right after `add_algorithm(1)` (n=3, alg1's epoch newly open), right
/// after `remove_algorithm(1)` (n=6, alg1's epoch newly closed), and at the
/// final tip (n=9) -- rather than growing past every size and asking a
/// reconstruction to reproduce it. `register_hasher`, which existed only to
/// feed that reconstruction's fold, is gone too.
#[test]
fn sg13_epochs_blob_matches_epochs_at() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg13/staging";
        let local = repo.to_thread_local();
        let mut log = new_log(&repo, staging, 2, FixtureHasher::new(32)).await;

        let mut trees: Vec<(u64, gix::ObjectId)> = vec![(
            0,
            support::ref_target(&local, staging).expect("genesis checkpoint must exist"),
        )];

        for i in 0..3u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        log.add_algorithm(1, Box::new(FixtureHasher::new(20)))
            .await
            .unwrap();
        trees.push((3, support::ref_target(&local, staging).unwrap()));

        for i in 3..6u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        log.remove_algorithm(1).await.unwrap(); // freeze alg1 at n=6
        trees.push((6, support::ref_target(&local, staging).unwrap()));

        for i in 6..9u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        trees.push((9, support::ref_target(&local, staging).unwrap()));

        // The full, currently-known epoch history of each algorithm.
        let full_epochs_alg0 = vec![(0u64, u64::MAX)];
        let full_epochs_alg1 = vec![(3u64, 6u64)];

        for (n, tree_n) in trees {
            for (alg_id, full_epochs) in [(0u64, &full_epochs_alg0), (1u64, &full_epochs_alg1)] {
                let view = AlgView {
                    hasher: Box::new(FixtureHasher::new(32)),
                    epochs: full_epochs.clone(),
                    frontier: Vec::new(),
                    frontier_coords: Vec::new(),
                };
                let expected = view.epochs_at(n);

                let epochs_tree = support::find_entry(&local, tree_n, "epochs").unwrap().oid;
                let blob_entry = support::find_entry(&local, epochs_tree, &hex(alg_id, 16));

                match expected {
                    None => {
                        // alg1 wasn't registered yet at this n. epochs_at
                        // only returns None pre-registration; alg0 is always
                        // registered from n=0, so this arm is alg1-only in
                        // this fixture.
                    },
                    Some(expected_epochs) => {
                        let bytes = support::read_blob(&local, blob_entry.unwrap().oid);
                        assert_eq!(
                            bytes.len() % 16,
                            0,
                            "n={n}, alg={alg_id}: epochs blob must be a multiple of 16 bytes"
                        );
                        let decoded: Vec<(u64, u64)> = bytes
                            .chunks_exact(16)
                            .map(|c| {
                                (
                                    u64::from_be_bytes(c[0..8].try_into().unwrap()),
                                    u64::from_be_bytes(c[8..16].try_into().unwrap()),
                                )
                            })
                            .collect();
                        assert_eq!(
                            decoded,
                            expected_epochs,
                            "n={n}, alg={alg_id}: epochs/{} must equal epochs_at({n})",
                            hex(alg_id, 16)
                        );
                    },
                }
            }
        }
    });
}

/// [SG16] A leaf's stored bytes MUST be byte-identical to the argument
/// `store_leaf` received, with no transformation, compression, or framing.
///
/// Rewritten against the key-derived layout's own leaf path
/// (`docs/specs/storage-git.md` §2.1: `leaves/<byte1-be-trim(index)>`)
/// instead of the retired `peaks/hex(0,2)/
/// hex(i,2)/leaf` navigation -- the claim under test (byte-for-byte
/// fidelity) is unchanged; only the path used to reach the stored blob is.
/// This is the sole place in the crate that checks byte fidelity straight
/// off the raw git blob, independent of `storage-git`'s own read path, with
/// adversarial payloads (embedded NUL, a length-prefix lookalike) chosen to
/// catch accidental framing: `key_derived_layout.rs`'s
/// `nodes_and_leaves_sit_exactly_at_their_derived_key_paths` checks only
/// that the *path set* under `leaves/` matches the written indices, never
/// blob content; `completeness_property.rs`'s `assert_every_key_matches`
/// compares `GitStorage::get_leaf`'s own decoded return value against
/// `MemoryStorage`, which goes through this crate's own read path rather
/// than the raw blob and so could not catch a framing bug applied
/// symmetrically on write and read.
#[test]
fn sg16_leaf_blob_is_byte_identical_to_input() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg16/staging";
        let mut log = new_log(&repo, staging, 2, FixtureHasher::new(32)).await;

        // Payloads chosen to catch any accidental framing: empty, binary
        // with embedded NUL, and bytes that look like a length prefix.
        let payloads: Vec<Vec<u8>> = vec![
            b"".to_vec(),
            vec![0u8, 1, 2, 0, 255, 0],
            b"\x00\x00\x00\x04abcd".to_vec(),
        ];

        for payload in &payloads {
            log.append_leaf(payload).await.unwrap();
        }

        let local = repo.to_thread_local();
        let tip = support::ref_target(&local, staging).unwrap();
        for (i, payload) in payloads.iter().enumerate() {
            let mut segments = vec!["leaves".to_string()];
            segments.extend(trimmed_key_segments(i as u64));
            let entry = support::resolve_path(&local, tip, &segments.join("/"))
                .unwrap_or_else(|| panic!("no leaf at {}", segments.join("/")));
            let bytes = support::read_blob(&local, entry.oid);
            assert_eq!(&bytes, payload, "leaf {i} must round-trip byte-identically");
        }
    });
}

/// The `byte1-be-trim` path scheme's own segment derivation, an independent
/// copy for this file alone (`acceptance_support/mod.rs` stays written from
/// `docs/specs/storage-git.md` alone; this scheme comes from the ratified
/// design instead, so it does not belong there) -- see
/// `key_derived_layout.rs`'s identical copy and its own doc comment for the
/// full derivation and citation.
fn trimmed_key_segments(key: u64) -> Vec<String> {
    let be = key.to_be_bytes();
    let first_nonzero = be.iter().position(|&b| b != 0).unwrap_or(7);
    let sig = &be[first_nonzero..];
    let mut segs = vec![sig.len().to_string()];
    segs.extend(sig.iter().map(|b| format!("{b:02x}")));
    segs
}

// [SG15] is not tested here. A node blob is opaque bytes stored and returned
// verbatim (per the spec); `storage-git`'s public API never carries a `Hasher`
// (SG26), so no width check can happen at this layer. Verbatim round-trip of
// hasher-produced nodes is covered by the differential tests' `get_node`
// parity; nothing here stores other lengths. Recorded here rather than faked
// with a test that could never go red.

/// [SG12] `meta` MUST have exactly one fixed length and layout for every
/// log, resumed or not, and that shape MUST be observable straight off the
/// blob's length -- no version-byte branching. A log that has never been
/// resumed and a log that has, each read from its own checkpoint tree, must
/// report the identical meta length.
#[test]
fn meta_blob_has_one_fixed_shape_regardless_of_resume_history() {
    smol::block_on(async {
        let dir_plain = tempfile::tempdir().unwrap();
        let repo_plain = bare_repo(dir_plain.path(), gix::hash::Kind::Sha256);
        let staging_plain = "refs/eml/storage/meta-shape-plain/staging";
        let mut plain = new_log(&repo_plain, staging_plain, 2, FixtureHasher::new(32)).await;
        for i in 0..5u32 {
            plain
                .append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let local_plain = repo_plain.to_thread_local();
        let plain_tip = support::ref_target(&local_plain, staging_plain).unwrap();
        let plain_meta_len = meta_len_at(&local_plain, plain_tip);

        // A resumed log: seal a small source log, resume onto a fresh
        // (empty) ref, then append a couple more (forward) leaves so the
        // checkpoint read back is not just the one write `resume` itself
        // performs.
        let dir_src = tempfile::tempdir().unwrap();
        let repo_src = bare_repo(dir_src.path(), gix::hash::Kind::Sha256);
        let staging_src = "refs/eml/storage/meta-shape-src/staging";
        let mut src = new_log(&repo_src, staging_src, 2, FixtureHasher::new(32)).await;
        for i in 0..3u32 {
            src.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
        }
        let sealed = src.seal().await.unwrap();

        let dir_dst = tempfile::tempdir().unwrap();
        let repo_dst = bare_repo(dir_dst.path(), gix::hash::Kind::Sha256);
        let staging_dst = "refs/eml/storage/meta-shape-dst/staging";
        let storage_dst = GitStorage::new(repo_dst.clone(), staging_dst, 2)
            .expect("open GitStorage over an empty ref");
        let mut resumed = NaryMerkleLog::resume(
            &sealed,
            storage_dst,
            vec![(0, Box::new(FixtureHasher::new(32)))],
        )
        .await
        .expect("resume onto an empty ref");
        resumed
            .append_subtree(&spine::Subtree::Leaf(b"fwd-0".to_vec()))
            .await
            .unwrap();
        resumed
            .append_subtree(&spine::Subtree::Leaf(b"fwd-1".to_vec()))
            .await
            .unwrap();

        let local_dst = repo_dst.to_thread_local();
        let dst_tip = support::ref_target(&local_dst, staging_dst).unwrap();
        let resumed_meta_len = meta_len_at(&local_dst, dst_tip);

        assert_eq!(
            resumed_meta_len, plain_meta_len,
            "a resumed log's meta blob must be the same fixed length as a log that has never been \
             resumed -- meta has exactly one shape"
        );
        assert_eq!(
            plain_meta_len, 10,
            "meta's one fixed shape carries no per-log resume marker, no version byte, and no \
             kind byte: arity and count alone -- 10 bytes, the same for every log regardless of \
             resume history"
        );
    });
}

fn meta_len_at(repo: &gix::Repository, tree: gix::ObjectId) -> usize {
    let meta_id = support::find_entry(repo, tree, "meta").unwrap().oid;
    support::read_blob(repo, meta_id).len()
}
