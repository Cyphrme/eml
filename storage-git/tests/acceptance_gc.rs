//! Acceptance tests for §5's garbage-collection safety, from
//! `docs/specs/storage-git.md` alone: SG22 (freshening an
//! already-existing object) and SG23 (post-write reachability). SG24 is
//! spec's own "Checked by: none" residual and is not testable by a runtime
//! test (see the note at the bottom of this file). SG22's own literal check
//! ("the backend implementation MUST cite this exact call in its own write
//! path") is spec-declared as a code-review check at implementation time,
//! not a runtime one; the test below instead checks the *outward,
//! observable* consequence SG22 exists to guarantee -- that a write does
//! not leave an already-existing, about-to-be-pruned object exactly as old
//! as it was.

#[path = "acceptance_support/mod.rs"]
mod support;

use std::time::SystemTime;

use support::{age_loose_object, bare_repo, loose_object_mtime, new_log};

/// [SG22] An object that already exists, unreferenced, and past the grace
/// period must not be silently left exactly as old as it was: this layer's
/// writes must freshen (rewrite) an object it is about to newly reference,
/// even when that exact content already has an object under the same id.
///
/// The `leaf` blob is the simplest fixture: its id is exactly
/// `git hash-object` of the raw leaf bytes (SG16, no framing), so writing
/// the identical payload through git's own convenience path first, ageing
/// its mtime, and then having `GitStorage` write the same payload as a real
/// leaf lets us observe whether `GitStorage`'s own write path touches
/// (freshens) that object rather than silently reusing it unchanged.
#[test]
fn sg22_writing_an_already_existing_object_freshens_it() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg22/staging";
        let local = repo.to_thread_local();
        let git_dir = dir.path().to_path_buf();

        let payload = b"sg22-freshen-me";
        // Pre-create the exact blob object git's own convenience path would
        // produce for this content, then age it far into the past.
        let blob_id = local.write_blob(payload).unwrap().detach();
        age_loose_object(&git_dir, blob_id);
        let aged_mtime = loose_object_mtime(&git_dir, blob_id)
            .expect("must be a loose object right after ageing it");
        assert!(
            aged_mtime < SystemTime::now() - std::time::Duration::from_secs(3600 * 24 * 300),
            "sanity: the object must actually be aged before the real write"
        );

        // GitStorage now writes a leaf with the identical payload, so the
        // `leaf` blob it newly references is content-identical (and thus
        // id-identical) to the pre-aged object.
        let mut log = new_log(&repo, staging, 2, support::FixtureHasher::new(32)).await;
        support::append_leaf(log.storage_mut(), 0, payload)
            .await
            .unwrap();

        // Compare against the aged sentinel captured above, not against a
        // `SystemTime::now()` taken immediately before the write: that
        // instrument races both wall-clock non-monotonicity and filesystem
        // mtime granularity, neither of which has anything to do with the
        // freshening behavior under test (this crate's own `gitutil.rs`
        // freshening probe, `write_object_refreshes_an_existing_objects_
        // mtime`, uses the identical deliberately-aged-sentinel pattern).
        // The margin here is the same ~300-day one the sanity check above
        // already established, wide enough that no non-freshening write
        // could cross it by clock skew or rounding.
        let after_mtime = loose_object_mtime(&git_dir, blob_id)
            .expect("the object must still exist as a loose object after GitStorage's write");
        assert!(
            after_mtime > aged_mtime + std::time::Duration::from_secs(3600 * 24 * 300),
            "SG22: GitStorage's write must freshen (rewrite) an object that already existed under \
             the same id, not silently leave it exactly as old as it was (aged sentinel: \
             {aged_mtime:?}, after write: {after_mtime:?})"
        );
    });
}

/// [SG23] After every batch, before returning success to the caller, every
/// object the batch newly references must be present. As the outward
/// postcondition of a successful write: once `write_batch` (or any
/// standalone method that goes through the identical path, SG18d) returns
/// `Ok`, every object reachable from the new checkpoint tree must resolve
/// in the object database -- nothing the write just made reachable may be
/// missing.
#[test]
fn sg23_every_object_a_successful_write_references_is_present() {
    smol::block_on(async {
        let dir = tempfile::tempdir().unwrap();
        let repo = bare_repo(dir.path(), gix::hash::Kind::Sha256);
        let staging = "refs/eml/storage/sg23/staging";
        let mut log = new_log(&repo, staging, 3, support::FixtureHasher::new(32)).await;
        log.add_algorithm(1, Box::new(support::FixtureHasher::new(20)))
            .await
            .unwrap();

        let local = repo.to_thread_local();
        for i in 0..17u32 {
            log.append_leaf(format!("leaf-{i}").as_bytes())
                .await
                .unwrap();
            let tip = support::ref_target(&local, staging).unwrap();
            support::assert_fully_reachable(&local, tip);
        }
    });
}

// SG24 ("a `git gc --prune=now` racing an in-flight write can still land in
// the SG22/SG23 freshening window") is the spec's own named residual gap:
// its own "Checked by" is explicitly "none -- this is an operational
// constraint on deployment, not a property this crate's test suite can
// exercise." No test is written for it here for that reason; the
// constraint's own text says it must appear in the crate's operational
// documentation instead of a test.
