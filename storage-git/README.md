# storage-git — git-backed storage

**A `polydigest::Storage` backend over a plain git object database.** `storage-git`
implements the `Storage` trait using [`gix`](https://github.com/GitoxideLabs/gitoxide)
directly against a git repository: every leaf and sealed node lives at a git
tree path derived only from its own key, behind one staging ref per log
instance. No commits, no application-level ref namespace, no dependency on
`git` shelling out.

## Role

This is the first of three layers a larger git-backed storage design
decomposes into (`docs/specs/storage-git.md` §"Status and scope"): raw
positional storage, laid out as git objects. A checkpoint library and
application layer, both out of this crate's scope, wrap this layer's tree
objects in commits and add ref namespaces, cadence, and retention policy.

## What this crate guarantees

- **Every stored key is content-addressed and permanent.** A node or leaf,
  once written, keeps its own path for the life of the log; there is no
  reconstruction step that can silently drop it (`docs/specs/storage-git.md`
  §2.1, §2.6).
- **A precondition violation is always an error, never a panic or a silent
  no-op.** `Storage::apply` rejects an out-of-order append, a duplicate
  algorithm registration, an unregistered removal/resume, and a
  `SeedFrontier` onto anything but a genuinely fresh store (SG18).
- **A compare-and-swap failure is classified correctly.** A genuine
  concurrent-writer race returns the distinguished tip-moved error; every
  other ref-update failure (a lock a concurrent `git gc`/`pack-refs` briefly
  holds, an I/O error) is retried internally up to a bound and then returned
  as a distinct transient error, never conflated with a real mismatch
  (SG19/SG19a).
- **A newly-written object is verified present before the write is
  considered durable**, closing the ordinary window between writing an
  object and it becoming reachable (SG22/SG23).

## An operator constraint this crate cannot enforce itself

**Do not run an immediate-expiry `git gc`/`git prune` (`--prune=now` or
equivalent) against a repository this crate is actively writing to.** Doing
so can race the narrow window between this crate's own freshening write and
the reference edit that makes the whole tree reachable again, and this
layer's object model has no way to close that window from inside the crate
-- it is the same constraint git documents for its own concurrent writers.
Git's default (non-zero) prune grace period is sufficient margin under this
crate's freshening and re-verification, and is the assumed operating
condition (SG24, `docs/specs/storage-git.md`).

## Checking these guarantees

The full normative contract is `docs/specs/storage-git.md`; each numbered
invariant (`SG1`, `SG2`, ...) names how it is checked, in its own *Checked
by:* clause. `cargo test -p storage-git` runs this crate's own suite for
quick iteration, but it is a partial check: the repository-wide acceptance
gate is `./check_acceptance.sh` from the repository root, and that is the
one that must exit 0 before a branch is considered green.

```sh
cargo test -p storage-git   # this crate's suite, for quick iteration
./check_acceptance.sh       # the repository's acceptance gate — run this before merging
```

## Place in the stack

```
merkle-spine → canonical-ml → polydigest → EML
                                  ↓
                           Storage trait
                                  ↓
              storage-git (this crate: git backend)
```

## Further reading

- `polydigest` — the combinator that defines the `Storage` interface
- [`docs/specs/storage-git.md`](../docs/specs/storage-git.md) — the normative
  specification this crate implements
- [`../docs/architecture.md`](../docs/architecture.md) — system design
