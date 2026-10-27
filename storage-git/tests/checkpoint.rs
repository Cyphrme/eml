//! Acceptance tests for checkpoint durability: `apply` syncs nothing, and a
//! new `GitStorage::checkpoint()` makes everything applied so far durable
//! by syncing it and recording the staging tip in the older of two
//! checkpoint refs (`ckpt/a`, `ckpt/b`, beside the staging ref). Opening a
//! store recovers from the on-disk states a crash or power loss can leave.
//!
//! ## Contract these tests fix (the implementation must match it)
//!
//! * `fn checkpoint(&mut self) -> Result<u64, GitStorageError>` returns the append count now
//!   durable.
//! * For a staging ref `refs/eml/storage/<name>/staging` the checkpoint refs are
//!   `refs/eml/storage/<name>/ckpt/a` and `.../ckpt/b`. Each targets the tree the staging ref
//!   targeted at that checkpoint (a tree, not a commit: a tree-targeted ref survives `git gc`,
//!   settled in the report).
//! * A checkpoint ref is *valid* when it resolves to a tree whose objects all read; the *newer*
//!   valid one is the one with the larger append count.
//! * `open` takes the newer valid checkpoint C. If staging resolves, its objects not reachable from
//!   C all read, it opens at staging and checkpoints; if staging is empty, torn, or an object is
//!   missing, it resets staging to C.
//!
//! No fsync seam is visible to an integration test (`gitutil::SYNCED` is
//! `cfg(test)` inside the crate), so sync behaviour is read from
//! `strace -f -y -e trace=fsync,fdatasync` over a child copy of this test
//! binary; the `child_*` tests below are those children and are `#[ignore]`.
//!
//! Run: `TMPDIR=$PWD/target/tmp cargo test -p storage-git --test checkpoint`

mod common;

use std::collections::BTreeSet;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use common::init_repo;
use gix::hash::Kind as HashKind;
use polydigest::Storage;
use storage_git::GitStorage;

const STAGING: &str = "refs/eml/storage/ck/staging";
const CKPT_A: &str = "refs/eml/storage/ck/ckpt/a";
const CKPT_B: &str = "refs/eml/storage/ck/ckpt/b";
const ENV_DIR: &str = "EML_CKPT_DIR";

// ---------------------------------------------------------------- helpers

fn git(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .arg("--git-dir")
        .arg(dir)
        .args(args)
        .stdin(Stdio::null())
        .output()
        .expect("run git");
    assert!(
        out.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

/// The object a ref resolves to, or `None` if absent or unparseable.
fn ref_val(dir: &Path, name: &str) -> Option<String> {
    let out = Command::new("git")
        .arg("--git-dir")
        .arg(dir)
        .args(["rev-parse", "--verify", "-q", name])
        .stderr(Stdio::null())
        .output()
        .expect("run git");
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).trim().to_string())
}

fn open(dir: &Path) -> Result<GitStorage, storage_git::GitStorageError> {
    GitStorage::open(dir, STAGING, 2)
}

fn len(s: &GitStorage) -> u64 {
    smol::block_on(s.append_count()).expect("append_count")
}

fn append(s: &mut GitStorage, i: u64) {
    smol::block_on(common::append_leaf(s, i, &i.to_le_bytes())).expect("append");
}

fn append_range(s: &mut GitStorage, range: std::ops::Range<u64>) {
    for i in range {
        append(s, i);
    }
}

fn loose_path(dir: &Path, oid: &str) -> PathBuf {
    dir.join("objects").join(&oid[..2]).join(&oid[2..])
}

fn tip(s: &GitStorage) -> String {
    s.tip_tree().expect("tip").to_string()
}

/// Objects reachable from tree `from` but not from tree `not`.
fn objects_only_in(dir: &Path, from: &str, not: &str) -> Vec<String> {
    git(dir, &["rev-list", "--objects", from, "--not", not])
        .lines()
        .map(|l| l.split(' ').next().unwrap().to_string())
        .collect()
}

/// Delete one loose blob reachable from `from` but not `not`: the state a
/// power loss leaves when a ref reached disk ahead of an object.
fn delete_a_blob_only_in(dir: &Path, from: &str, not: &str) {
    // A leaf blob, not `meta`: opening must get past the cheap reads and
    // still notice the hole.
    let listing = git(dir, &["rev-list", "--objects", from, "--not", not]);
    let victim = listing
        .lines()
        .find_map(|l| l.split_once(' ').filter(|(_, p)| p.starts_with("leaves/")))
        .map(|(o, _)| o.to_string())
        .expect("a leaf blob unique to the newer tree");
    std::fs::remove_file(loose_path(dir, &victim)).expect("delete loose blob");
}

fn tear_ref(dir: &Path, name: &str, bytes: &[u8]) {
    let p = dir.join(name);
    assert!(p.is_file(), "{name} must be a loose ref to tear it");
    std::fs::write(p, bytes).expect("tear ref");
}

/// A bare repository holding three nested states of one log:
/// `c1` (3 leaves) is contained in `c2` (6) is contained in `s` (9), with
/// staging at `s`. No checkpoint refs exist; tests write them directly.
struct Fixture {
    _td: tempfile::TempDir,
    dir: PathBuf,
    c1: String,
    c2: String,
    s: String,
}

fn fixture() -> Fixture {
    let (td, repo) = init_repo(HashKind::Sha1);
    let dir = td.path().to_path_buf();
    let mut st = GitStorage::new(repo, STAGING, 2).unwrap();
    append_range(&mut st, 0..3);
    let c1 = tip(&st);
    append_range(&mut st, 3..6);
    let c2 = tip(&st);
    append_range(&mut st, 6..9);
    let s = tip(&st);
    Fixture {
        _td: td,
        dir,
        c1,
        c2,
        s,
    }
}

/// Recovery must leave a usable store: the next append lands at `len`.
fn assert_writable(mut st: GitStorage) {
    let n = len(&st);
    append(&mut st, n);
    assert_eq!(len(&st), n + 1);
}

// ----------------------------------------------- strace-observed children

struct Traced {
    lines: Vec<String>,
    stdout: String,
}

/// Re-run this binary's `#[ignore]` test `scenario` under strace.
fn run_traced(scenario: &str, dir: &Path) -> Traced {
    let td = tempfile::tempdir().unwrap();
    let log = td.path().join("strace.out");
    let out = Command::new("strace")
        .args(["-f", "-y", "-qq", "-e", "trace=fsync,fdatasync,%file", "-o"])
        .arg(&log)
        .arg(std::env::current_exe().unwrap())
        .args(["--exact", scenario, "--ignored", "--nocapture"])
        .args(["--test-threads=1"])
        .env(ENV_DIR, dir)
        .stdin(Stdio::null())
        .output()
        .expect("strace must be installed to observe fsync");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    let lines: Vec<String> = std::fs::read_to_string(&log)
        .expect("strace log")
        .lines()
        .map(str::to_string)
        .collect();
    assert!(
        out.status.success(),
        "child {scenario} failed ({:?}); it never reached its end.\nstdout: {stdout}\nstderr: \
         {stderr}",
        out.status
    );
    Traced { lines, stdout }
}

fn mark(name: &str) {
    let _ = std::fs::metadata(format!("/__eml_mark_{name}"));
}

impl Traced {
    fn mark_at(&self, name: &str) -> usize {
        let needle = format!("__eml_mark_{name}\"");
        self.lines
            .iter()
            .position(|l| l.contains(&needle))
            .unwrap_or_else(|| panic!("child never reached mark {name}"))
    }

    /// Paths fsynced strictly between marks `from` and `to`.
    fn fsyncs_between(&self, from: &str, to: &str) -> Vec<String> {
        let (a, b) = (self.mark_at(from), self.mark_at(to));
        self.lines[a + 1..b]
            .iter()
            .filter(|l| l.contains(" fsync(") || l.contains(" fdatasync("))
            .map(|l| {
                let (s, e) = (l.find('<').unwrap(), l.find('>').unwrap());
                l[s + 1..e].to_string()
            })
            .collect()
    }

    fn out(&self, key: &str) -> String {
        let prefix = format!("OUT {key}=");
        self.stdout
            .lines()
            .find_map(|l| l.strip_prefix(&prefix))
            .unwrap_or_else(|| panic!("child printed no {key}"))
            .trim()
            .to_string()
    }
}

fn child_dir() -> PathBuf {
    PathBuf::from(std::env::var(ENV_DIR).expect("child run by its parent test only"))
}

/// Child for test 1: applies only, never checkpoints.
#[test]
#[ignore = "child process of apply_performs_zero_fsyncs"]
fn child_apply_only() {
    let mut st = open(&child_dir()).unwrap();
    mark("a");
    append_range(&mut st, 0..6);
    mark("b");
}

/// Child for test 2: two applies-then-checkpoint rounds.
#[test]
#[ignore = "child process of checkpoint_syncs_exactly_what_was_applied_since_the_last"]
fn child_two_checkpoints() {
    let mut st = open(&child_dir()).unwrap();
    append_range(&mut st, 0..4);
    let l1 = st.checkpoint().unwrap();
    println!("OUT len1={l1}");
    println!("OUT tip_a={}", tip(&st));
    mark("a");
    // One batch, so no intermediate tree is written that the tip does not
    // reach: the expected sync set is then exactly the tip-reachable delta.
    let datas: Vec<[u8; 8]> = (4u64..8).map(u64::to_le_bytes).collect();
    let ops: Vec<polydigest::WriteOp<'_>> = (4u64..8)
        .zip(&datas)
        .map(|(at, data)| polydigest::WriteOp::AppendLeaf {
            at,
            data,
            nodes: &[],
        })
        .collect();
    smol::block_on(st.apply(&ops)).unwrap();
    mark("b");
    let l2 = st.checkpoint().unwrap();
    mark("c");
    println!("OUT len2={l2}");
    println!("OUT tip_b={}", tip(&st));
}

/// Child for test 6: checkpoints forever, reporting each durable length.
#[test]
#[ignore = "child process of a_killed_writer_reopens_at_or_past_its_last_checkpoint"]
fn child_writer_loop() {
    use std::io::Write as _;
    let mut st = open(&child_dir()).unwrap();
    for i in 0u64.. {
        append(&mut st, i);
        if i % 3 == 2 {
            let l = st.checkpoint().unwrap();
            let mut so = std::io::stdout().lock();
            writeln!(so, "OUT ckpt={l}").unwrap();
            so.flush().unwrap();
        }
    }
}

// ------------------------------------------------------------------ tests

/// 1. `apply` performs zero fsyncs.
#[test]
fn apply_performs_zero_fsyncs() {
    let (td, _repo) = init_repo(HashKind::Sha1);
    let t = run_traced("child_apply_only", td.path());
    let synced = t.fsyncs_between("a", "b");
    assert!(
        synced.is_empty(),
        "apply must not fsync; {} fsyncs, first: {:?}",
        synced.len(),
        synced.first()
    );
}

/// 2. `checkpoint()` syncs every object (and its fan-out directory) written
/// since the previous checkpoint, nothing from before it, and returns the
/// durable length.
#[test]
fn checkpoint_syncs_exactly_what_was_applied_since_the_last() {
    let (td, _repo) = init_repo(HashKind::Sha1);
    let dir = td.path().canonicalize().unwrap();
    let t = run_traced("child_two_checkpoints", &dir);
    let (tip_a, tip_b) = (t.out("tip_a"), t.out("tip_b"));
    assert_eq!(t.out("len1"), "4");
    assert_eq!(t.out("len2"), "8", "returns the durable length");

    let synced: BTreeSet<String> = t.fsyncs_between("b", "c").into_iter().collect();
    let new: Vec<String> = objects_only_in(&dir, &tip_b, &tip_a);
    let new_files: BTreeSet<String> = new
        .iter()
        .map(|o| loose_path(&dir, o).to_string_lossy().into_owned())
        .collect();
    let missing: Vec<_> = new_files.difference(&synced).collect();
    assert!(
        missing.is_empty(),
        "written since the last checkpoint, never synced: {missing:?}"
    );
    for o in &new {
        let fanout = dir
            .join("objects")
            .join(&o[..2])
            .to_string_lossy()
            .into_owned();
        assert!(synced.contains(&fanout), "fan-out dir {fanout} not synced");
    }
    assert!(
        synced.contains(&dir.join("objects").to_string_lossy().into_owned()),
        "objects dir not synced"
    );
    // Everything the first checkpoint covered stays unsynced the second time.
    let earlier: BTreeSet<String> = git(&dir, &["rev-list", "--objects", &tip_a])
        .lines()
        .map(|l| {
            loose_path(&dir, l.split(' ').next().unwrap())
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    let stale: Vec<_> = synced.intersection(&earlier).collect();
    assert!(
        stale.is_empty(),
        "object files synced that predate the previous checkpoint: {stale:?}"
    );
}

/// 3a. An object reachable from staging, not from the checkpoint, is gone:
/// staging resets to the newest checkpoint.
#[test]
fn recovery_resets_staging_when_a_reachable_object_is_missing() {
    let f = fixture();
    git(&f.dir, &["update-ref", CKPT_A, &f.c1]);
    git(&f.dir, &["update-ref", CKPT_B, &f.c2]);
    delete_a_blob_only_in(&f.dir, &f.s, &f.c2);

    let st = open(&f.dir).expect("open must recover, not fail");
    assert_eq!(
        len(&st),
        6,
        "reset to the newest checkpoint (6), not staging (9) or the older (3)"
    );
    assert_eq!(ref_val(&f.dir, STAGING).as_deref(), Some(f.c2.as_str()));
    assert_writable(st);
}

/// 3b. Staging is empty or torn: reset to the newest checkpoint.
#[test]
fn recovery_resets_staging_when_the_ref_is_empty_or_torn() {
    for torn in [&b""[..], &b"3f2a9c"[..]] {
        let f = fixture();
        git(&f.dir, &["update-ref", CKPT_A, &f.c1]);
        git(&f.dir, &["update-ref", CKPT_B, &f.c2]);
        tear_ref(&f.dir, STAGING, torn);

        let st = open(&f.dir).unwrap_or_else(|e| panic!("torn staging {torn:?}: open failed: {e}"));
        assert_eq!(len(&st), 6, "torn staging {torn:?}");
        assert_eq!(ref_val(&f.dir, STAGING).as_deref(), Some(f.c2.as_str()));
        assert_writable(st);
    }
}

/// 3c. The newer checkpoint ref is torn: the older valid one is used.
#[test]
fn recovery_uses_the_older_checkpoint_when_the_newer_is_torn() {
    let f = fixture();
    git(&f.dir, &["update-ref", CKPT_A, &f.c1]);
    git(&f.dir, &["update-ref", CKPT_B, &f.c2]);
    tear_ref(&f.dir, CKPT_B, b"");
    delete_a_blob_only_in(&f.dir, &f.s, &f.c1);

    let st = open(&f.dir).expect("open must recover, not fail");
    assert_eq!(
        len(&st),
        3,
        "older valid checkpoint (3), not the torn newer (6)"
    );
    assert_eq!(ref_val(&f.dir, STAGING).as_deref(), Some(f.c1.as_str()));
    assert_writable(st);
}

/// 3d. Process-crash state: every object present, staging ahead of the
/// checkpoint. Open at staging, and checkpoint it (into the older ref).
#[test]
fn recovery_keeps_an_intact_staging_ahead_of_the_checkpoint_and_checkpoints_it() {
    let f = fixture();
    git(&f.dir, &["update-ref", CKPT_A, &f.c1]);
    git(&f.dir, &["update-ref", CKPT_B, &f.c2]);

    let st = open(&f.dir).expect("open");
    assert_eq!(len(&st), 9, "intact staging is kept");
    assert_eq!(ref_val(&f.dir, STAGING).as_deref(), Some(f.s.as_str()));
    let (a, b) = (ref_val(&f.dir, CKPT_A), ref_val(&f.dir, CKPT_B));
    assert_eq!(
        (a.as_deref(), b.as_deref()),
        (Some(f.s.as_str()), Some(f.c2.as_str())),
        "open checkpointed staging over the older ref (a), keeping the newer (b)"
    );
    assert_writable(st);
}

/// 4. Checkpoints alternate between the two refs, overwriting the older.
#[test]
fn checkpoints_alternate_between_the_two_refs() {
    let (td, repo) = init_repo(HashKind::Sha1);
    let dir = td.path();
    let mut st = GitStorage::new(repo, STAGING, 2).unwrap();
    let both = |d: &Path| (ref_val(d, CKPT_A), ref_val(d, CKPT_B));

    append_range(&mut st, 0..2);
    let t1 = tip(&st);
    assert_eq!(st.checkpoint().unwrap(), 2);
    let (a, b) = both(dir);
    assert!(
        matches!((&a, &b), (Some(x), None) | (None, Some(x)) if *x == t1),
        "first checkpoint writes exactly one ref: {a:?} {b:?}"
    );

    append_range(&mut st, 2..4);
    let t2 = tip(&st);
    assert_eq!(st.checkpoint().unwrap(), 4);
    let (a, b) = both(dir);
    let set: BTreeSet<_> = [a.clone(), b.clone()].into_iter().flatten().collect();
    assert_eq!(
        set,
        BTreeSet::from([t1.clone(), t2.clone()]),
        "second goes to the other ref"
    );

    append_range(&mut st, 4..6);
    let t3 = tip(&st);
    assert_eq!(st.checkpoint().unwrap(), 6);
    let (a, b) = both(dir);
    let set: BTreeSet<_> = [a, b].into_iter().flatten().collect();
    assert_eq!(
        set,
        BTreeSet::from([t2, t3]),
        "third overwrites the older (first) ref"
    );
}

/// 5a. A checkpoint after `git pack-refs --all` (the loose staging ref is
/// gone) succeeds, and its ref survives a reopen.
#[test]
fn checkpoint_succeeds_after_refs_are_packed() {
    let (td, repo) = init_repo(HashKind::Sha1);
    let dir = td.path();
    let mut st = GitStorage::new(repo, STAGING, 2).unwrap();
    append_range(&mut st, 0..3);
    git(dir, &["pack-refs", "--all"]);
    assert!(
        !dir.join(STAGING).exists(),
        "precondition: staging ref is no longer loose"
    );

    assert_eq!(
        st.checkpoint()
            .expect("checkpoint with a packed staging ref"),
        3
    );
    let t = tip(&st);
    drop(st);
    let held = [ref_val(dir, CKPT_A), ref_val(dir, CKPT_B)];
    assert!(
        held.iter().flatten().any(|v| *v == t),
        "no checkpoint ref holds the tip: {held:?}"
    );
    assert_eq!(len(&open(dir).unwrap()), 3);
}

/// 5b. A sync failure is never reported for an apply whose CAS landed: with
/// `pack-refs` racing the writer, every `apply` is `Ok`, or fails with the
/// ref unmoved. (Probabilistic; the deterministic half is test 1.)
#[test]
fn apply_never_reports_failure_for_a_write_that_landed() {
    use std::sync::atomic::{AtomicBool, Ordering};
    let (td, repo) = init_repo(HashKind::Sha1);
    let dir = td.path().to_path_buf();
    let stop = std::sync::Arc::new(AtomicBool::new(false));
    let (s2, d2) = (stop.clone(), dir.clone());
    let packer = std::thread::spawn(move || {
        while !s2.load(Ordering::Relaxed) {
            let _ = Command::new("git")
                .arg("--git-dir")
                .arg(&d2)
                .args(["pack-refs", "--all"])
                .status();
        }
    });
    let mut st = GitStorage::new(repo, STAGING, 2).unwrap();
    let mut bad = Vec::new();
    let mut i = 0u64;
    while i < 120 {
        let before = ref_val(&dir, STAGING);
        match smol::block_on(common::append_leaf(&mut st, i, &i.to_le_bytes())) {
            Ok(()) => i += 1,
            Err(e) if e.is_tip_moved() => panic!("single writer saw a tip move: {e}"),
            Err(e) => {
                let after = ref_val(&dir, STAGING);
                if after != before {
                    bad.push(format!("apply {i} failed ({e}) but the ref moved"));
                }
                break;
            },
        }
    }
    stop.store(true, Ordering::Relaxed);
    packer.join().unwrap();
    assert!(bad.is_empty(), "{bad:?}");
    assert_eq!(
        i, 120,
        "an apply failed outright under concurrent pack-refs"
    );
}

/// 6. SIGKILL a writer mid-run; the store reopens at or past the last
/// length it reported durable, and verifies.
#[test]
fn a_killed_writer_reopens_at_or_past_its_last_checkpoint() {
    let (td, _repo) = init_repo(HashKind::Sha1);
    let dir = td.path().to_path_buf();
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "child_writer_loop",
            "--ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(ENV_DIR, &dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut lines = BufReader::new(child.stdout.take().unwrap()).lines();
    let mut last = 0u64;
    let mut seen = 0;
    while seen < 8 {
        match lines.next() {
            Some(Ok(l)) => {
                if let Some(v) = l.strip_prefix("OUT ckpt=") {
                    last = v.parse().unwrap();
                    seen += 1;
                }
            },
            _ => break,
        }
    }
    child.kill().unwrap();
    let out = child.wait_with_output().unwrap();
    assert_eq!(
        seen,
        8,
        "writer reported {seen} checkpoints before dying; stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let st = open(&dir).expect("reopen after SIGKILL");
    assert!(
        len(&st) >= last,
        "reopened at {} < last durable {last}",
        len(&st)
    );
    git(&dir, &["fsck", "--strict", "--no-dangling"]);
    let t = st.tip_tree().unwrap();
    let repo = gix::ThreadSafeRepository::open(&dir)
        .unwrap()
        .to_thread_local();
    fn reach(repo: &gix::Repository, id: gix::ObjectId) {
        let obj = repo
            .find_object(id)
            .expect("object reachable from the tip must read");
        if obj.kind == gix::objs::Kind::Tree {
            for e in obj.into_tree().decode().unwrap().entries {
                reach(repo, e.oid.to_owned());
            }
        }
    }
    reach(&repo, t);
    assert_writable(st);
}
