# SPEC: storage-git — the git storage backend

## Status and scope

This is the normative specification for `storage-git`, a backend crate that
implements `polydigest`'s `Storage` trait (`polydigest/src/storage.rs`) over a
git object database reached through `gix`, pinned to `gix = "=0.87.1"`. It is
the first of three layers a larger git-backed storage design decomposes into:

1. **This layer.** Raw positional storage: leaves and sealed node digests,
   laid out as git objects, behind the unmodified `Storage` trait plus a small
   set of git-native additions (compare-and-swap writes, historical reads, and
   a tree-object accessor). No commits. No refs other than one staging ref per
   log instance. No application policy.
2. **A checkpoint library** (out of scope here). Wraps this layer's tree
   objects in commits, enforces the checkpoint chain's forward-only
   compare-and-swap, carries an application's retention parents and companion
   ref edits, and exposes the extension proof between checkpoints. It depends
   on this layer; this layer has no dependency on it and no knowledge of
   commits, parents, or refs beyond its own staging ref.
3. **Applications** (out of scope here). Ref namespaces, checkpoint cadence,
   commit metadata, and any content committed alongside a checkpoint (for
   example a git-tree-ingestion mirror that computes its own Merkle
   commitment over an arbitrary directory). None of that is specified by this
   document, and this crate MUST NOT depend on any of it.

**Why the split matters here.** Security in this design comes from the
Merkle commitments `polydigest` computes and from the hash algorithm the
caller chooses over them — never from git's own object hash. This layer
therefore treats git purely as a content-addressed object store: a place to
put bytes and immutable trees and to move one pointer forward under a
precondition. It never trusts a git object id as a security boundary, and
nothing it specifies depends on which object-hash format (SHA-1 or SHA-256)
the repository uses. A verifier's trust rests entirely on the per-algorithm
digests this layer stores and the caller's own recomputation over bytes it
actually reads back — not on git.

**Why no commits.** A commit's parents, author, and message are Axios-shaped
policy decisions (retention parents, checkpoint cadence, view chains) that
belong to the checkpoint library and the application above it, never to raw
storage. This layer's staging ref therefore points **directly at a git tree
object**, not at a commit. `gix` places no kind restriction on a reference's
target (§4.2), so this is a supported, not an incidental, use of git.

**Why redaction-freedom matters.** The log this layer stores is meant to
serve as one state in a chain whose extension can be proved and whose
soundness is quantified over that extension alone; rewriting a past state
breaks the chain the same way redacting an entry in any append-only ledger
does. This layer does not itself enforce forward-only history — that is the
checkpoint library's job, built on the compare-and-swap primitive this layer
exposes (§4.2) — but every design choice below is made so that primitive is
sufficient to build it on.

Everything under §2–§7 is the literal target of this document. §8 records
what is deliberately excluded, with its own rationale, so a reader does not
mistake omission for oversight.

## 1. Notation

- `hex(x, w)` — the non-negative integer `x` rendered as lowercase
  hexadecimal, zero-padded to exactly `w` digits.
- `H` — an algorithm's digest function, as supplied through `spine::Hasher`
  by the caller. `H`'s output width is `Hasher::digest_len()` for that
  algorithm and is never assumed by this layer.
- `k` — the log's arity, `2 <= k <= 256` (`spine::ARITY_RANGE`,
  `spine/src/topology.rs:27`).
- `n` — the log's global size: the number of appended items (`polydigest`'s
  `count`, `Storage::len()`).
- `alg_id` — a `u64` algorithm identifier, opaque to this layer.
- `T(left, h)` — the sealed perfect `k`-ary subtree covering item indices
  `[left, left + k^h)`. `T(left, 0)` is a single item's node.
- `C(n)` — the checkpoint tree: the complete, self-describing git tree
  recording the log's state at size `n` (§2.1).
- **Materialized** node — a `T(left, h)` this backend has itself built down
  to real payload bytes (`h = 0`) or real children (`h > 0`).
- **Opaque** node — a `T(left, h)` this backend knows only by digest, never
  having stored the bytes or children beneath it (§2.6).

Every constraint below is tagged `SG<n>` and states how it is checked. A tag
of **property test** or **golden vector** names a check this crate's test
suite MUST carry once implemented; **structural** names a fact enforced by
the object layout itself (violating it produces an object no reader can
parse as this layout, not merely a wrong one); **compiled probe** cites a
`gix` behavior already confirmed by compiling against the pinned tag, not
merely read from source or documentation.

## 2. The git object layout

### 2.1 The checkpoint tree

```
C(n)                          tree
  meta                        blob    §3
  epochs/                     tree    one blob per ever-registered algorithm
    hex(alg_id, 16)           blob    §3
  roots/                      tree    one blob per algorithm active at n
    hex(alg_id, 16)           blob    §3
  peaks/                      tree
    hex(j, 2)/                tree    one per base-k digit position j of n
                                       with digit d_j > 0
      hex(q, 2)                tree   T(left, j), for q = 0 .. d_j - 1,
                                       left to right
```

**[SG1]** `C(n)` MUST be a git tree object with exactly the four top-level
entries `meta` (blob), `epochs` (tree), `roots` (tree), and `peaks` (tree),
present even when empty (an empty `roots`/`epochs`/`peaks` tree is the empty
git tree object, one fixed object id per repository object-hash format).
*Checked by: structural — any C(n) reader that does not find exactly these
four entries MUST reject the object as malformed; golden vector against a
handful of representative `n`.*

**[SG2]** For each base-`k` digit position `j` (the frontier height) where
`n`'s base-`k` representation has a nonzero digit `d_j`, `peaks/hex(j, 2)`
MUST exist and MUST contain exactly `d_j` entries, named `hex(0, 2)` through
`hex(d_j - 1, 2)`, each a tree entry whose object id equals `T(left, j)` for
the corresponding peak, in the same left-to-right order the log's frontier
carry produces (`spine::frontier_for_size`, `spine/src/topology.rs:74`;
`cml::reduction_count`, `cml/src/schedule.rs:11`). No `peaks/hex(j, 2)` entry
MUST exist for a digit position whose digit is zero. *Checked by: property
test — for every `n` up to a bound, the peak set derived from `peaks/`
MUST equal `frontier_for_size(n, k)`.*

Two hex digits bound both `j` (frontier height, at most `64` for `k = 2` and
far less for larger `k`, well under `255`) and `q` (a peak ordinal, at most
`k - 1 <= 255`) within their declared range without ambiguity.

### 2.2 A sealed node, `T(left, h)`

```
T(left, 0)                    tree
  leaf                        blob    the raw item bytes, verbatim
                                       (present only if materialized, §2.6)
  digest/                     tree
    hex(alg_id, 16)           blob    H(leaf), one per algorithm active
                                       at index `left`

T(left, h > 0)                tree
  hex(c, 2)                   tree    child T(left + c*k^(h-1), h-1),
                                       for c = 0 .. k-1
                                       (present for c = 0 .. k-1 together,
                                       once every child slot has a known
                                       occupant -- §2.6)
  digest/                     tree
    hex(alg_id, 16)           blob    the algorithm's node digest over
                                       [left, left + k^h), one per algorithm
                                       whose active range over that interval
                                       is non-empty
```

**[SG3]** `T(left, h)` MUST carry a `digest/` subtree naming, for every
algorithm `a` where `active_range(a, left, left + k^h)` holds
(`cml::engine::AlgView::active_range`, `cml/src/engine.rs:159-165`), a blob
at `digest/hex(alg_id, 16)` equal to that algorithm's node digest over the
range: `H_a(leaf bytes)` at `h = 0`, `node(a, …)` folded over the `k`
children at `h > 0`. **No entry MUST exist under `digest/` for an algorithm
whose active range over `[left, left + k^h)` is empty** — such a value is
the algorithm's null constant and is reconstructed by the reader, never
stored (mirrors `get_node_hash`'s corruption rule, `cml/src/engine.rs:262-298`:
absence in an active range is corruption, absence in an inactive range is
the null constant). *Checked by: property test against
`cml::engine::get_node_hash`'s null/corruption split.*

The degenerate case — **every** algorithm's active range over
`[left, left + k^h)` is empty, so `digest/` itself is empty — is not
corruption either. It arises whenever every algorithm that ever covered a
frontier coordinate is removed before a write that still needs that
coordinate to exist structurally (`frontier_for_size` depends only on the
total count, never on which algorithms are active), most reachably through
`polydigest::NaryMerkleLog::resume`, which gates each pushed node digest on
the covering algorithm's own still-open epoch rather than on the coordinate
merely belonging to the resumed frontier. This layer MUST build such a
coordinate the same way it builds any other opaque node with nothing handed
to it: `digest/` present and empty, no `leaf`, no children — never a
`Corruption` error, since a git-native frontier position with zero live
digests is exactly what `MemoryStorage` already represents by recording
nothing for it at all.

**[SG4]** `T(left, 0)` MAY carry a `leaf` blob, present iff this layer was
ever given the leaf's own bytes (§2.6). `T(left, h > 0)` MAY carry
`hex(c, 2)` child entries for `c = 0..k-1`, present together, all or none,
iff this layer has *some* occupant for **every** child slot — materialized or
opaque alike (§2.6's decomposition rule) — never gated on whether a known
child, or anything beneath it, is itself opaque rather than materialized. A
coordinate with a known occupant for only *some* of its child slots is not
reachable in practice (a merge only ever combines peaks that are each
already known), so this layer never has to decide what such a coordinate
would look like. A `digest/`
subtree alone, with no `leaf` and no `hex(c, 2)` children at all, is a
**structurally valid, opaque** node: the only way this arises is a
coordinate whose digest arrived as one atomic, undecomposed unit with
nothing known about any child slot at all (a resumed log's genesis peak, or
a single subtree append — §2.6). *Checked by: structural.*

### 2.3 Entry modes and canonical order

**[SG5]** Every blob entry (`meta`, an `epochs/roots/digest` leaf, `leaf`)
MUST use mode `100644` (regular, non-executable). Every tree entry (`epochs`,
`roots`, `peaks`, a `peaks/hex(j,2)` group, `digest`, a `hex(c,2)` child)
MUST use mode `40000`. Nothing this layer writes is ever a symlink or a
gitlink. *Checked by: structural; `gix::objs::tree::EntryKind::{Blob,Tree}`
already normalize to exactly these two canonical mode strings
(`gix-object/src/tree/mod.rs`, confirmed by compiling a check against the pinned tag).*

**[SG6]** Every sibling group this layer writes uses **fixed-width names**:
16 hex digits for `hex(alg_id, 16)`, 2 hex digits for `hex(j, 2)`, `hex(q, 2)`,
and `hex(c, 2)`, or a fixed literal (`meta`, `epochs`, `roots`, `peaks`,
`leaf`, `digest`). No name is ever a prefix of a sibling's name, so git's
canonical tree order — which sorts a directory entry as if its name carried
a trailing separator (`gix-object/src/tree/mod.rs::name_order`) — coincides
with plain byte-lexicographic order on every level this layer builds, and no
entry's serialization depends on whether a sibling is a blob or a tree.
*Checked by: structural — a name-collision or prefix-ambiguity check is
exhaustive over the fixed alphabet.*

**[SG7]** `gix::objs::Tree::write_to` does **not** sort entries; it only
`debug_assert!`s that they arrive pre-sorted, a check compiled out of release
builds (`gix-object/src/tree/write.rs`, confirmed by reading the pinned tag's
source — not merely asserted from documentation). This layer MUST therefore
sort every `Tree`'s `entries` by git's canonical order itself before calling
any `gix` write function, in every build profile. *Checked by: property
test — construct a tree from a deliberately-unsorted entry vector and assert
the written object id matches the id produced from the same entries
pre-sorted by hand; a release-mode test run is required, since the failure
this constraint prevents is invisible in debug builds.*

### 2.4 Position lookup

**[SG8]** To read item `i` at tree size `n` (`i < n`): walk `n`'s base-`k`
digits from the highest nonzero position down, subtracting `d_j * k^j` from a
running offset until `i` falls inside a peak group's covered range, giving a
peak `T(left, j)` at ordinal `q` within `peaks/hex(j, 2)`. Then descend `j`
levels from that peak, at each level taking child `hex(c, 2)` where `c` is
digit `h - 1` of `(i - left)` written in base `k`, until reaching `T(left', 0)`.
The full git path is
`peaks/hex(j,2)/hex(q,2)/hex(c_{j-1},2)/…/hex(c_0,2)/leaf` (or `digest/…` for
a digest read). Every such path resolves, because every aligned block
`[left, left + k^h)` with `left + k^h <= n` was sealed the moment it
completed and is never rewritten (`cml::engine::carry`,
`cml/src/engine.rs:238-280`). *Checked by: property test — for every valid
`(n, i)`, the path derived from `frontier_for_size` and base-`k` digit
descent MUST resolve to a leaf/digest whose value matches an independent,
non-git reference implementation's (e.g. `MemoryStorage`) value for the same
`(n, i)`.*

### 2.5 Purity

**[SG9]** `C(n)`'s object id (per object-hash format) MUST be a pure
function of exactly: `k`, the item sequence `0..n`, the **currently known**
epoch history of every registered algorithm truncated to `n`
(`cml::engine::AlgView::epochs_at`, `cml/src/engine.rs:196-217`), and the log
kind byte (§3.1) — except at `n == 0`, where `meta.kind` is fixed to the
canonical value `0x00` for every log, regardless of what kind it is bound
to or will ever be bound to (§3.1's note). It MUST NOT depend on insertion
order among operations that do not change `n` (for example two algorithm
registrations at the same size, in either order, yield the same `C(n)` once
both are known), on wall-clock time, on writer identity — including *how
many times* a writer has reopened the log — or, at `n == 0` specifically,
on which kind of append (leaf or subtree) the log's history goes on to make
first. *Checked by: property test — build the same log through two
different operation orderings that reach an identical logical state, and
require identical `C(n)` object ids; separately, a continuous writer and a
writer that reopens through a plain open at arbitrary points over an
identical operation sequence must reach byte-identical `C(n)` for every
`n`; and, separately again, two logs with byte-identical (empty) content at
`n == 0` must reach the identical `C(0)` even when one log's first-ever
append is a leaf and the other's is a subtree.*

One consequence of SG9 is worth stating precisely, because the exhibit's
`C(n)` notation can otherwise be misread as "one object per size, forever."
It is not: a size `n` reached before some later algorithm registration and
the same size `n` reached after it are two different logical states and two
different `C(n)` objects, related only by both truncating the same
underlying epoch history to `n` via `epochs_at`. `tree_at(n)` (§4.3) always
returns the object for the **current** state's projection to `n`, never a
stale intermediate one, and any intermediate object a partial write left
behind is simply unreferenced and eligible for collection (§5).

### 2.6 Materialized versus opaque nodes

**[SG10]** At `h = 0`, a `T(left, 0)` node built from `Storage::store_leaf`
MUST carry `leaf` (materialized); one built from `Storage::store_node` with
no corresponding `store_leaf` call — which is exactly what happens for every
`cml::LogKind::Subtree` append (`polydigest::NaryMerkleLog::append_subtree`,
`polydigest/src/tree.rs:821-868`, calls only `store_node`, never
`store_leaf`) — MUST be opaque: `digest/` only, no `leaf`. At `h > 0`, a
`T(left, h)` node MUST carry a `hex(c, 2)` child entry for **every** `c`
iff this layer has a known occupant for every child slot at once — the
node decomposes as a whole, never one slot at a time (§2.1's
`resolve_node`, `is_decomposable` in `src/build.rs`, requires
`(0..k).all(..)`). Decomposition is never gated on whether a known
child (or anything beneath it) is itself opaque rather than
materialized. A child slot has a known occupant when this batch was
given a digest or leaf bytes for it, or when the prior write's own tree
already names an occupant for it (SG18a) — regardless of whether that
occupant is itself opaque or carries further structure. A coordinate
arriving with **no** known occupant for *any* child slot — a resumed log's
genesis peak (`polydigest::NaryMerkleLog::resume`,
`polydigest/src/tree.rs:151-260`, persists only frontier peaks, never
historical leaves, and only ever onto a fresh backend) or a single subtree
append's own root — stays a pure `digest/`-only opaque leaf shape, since
there is nothing to decompose it with; so does a coordinate with a known
occupant for only *some* of its child slots, though that case does not
arise in practice — a merge only ever combines peaks that are each
already known, so a partially-known coordinate has no path into the
frontier this layer ever sees. This is what makes a mixed
subtree — some descendants opaque (inherited, or from a subtree append),
others materialized (an ordinary forward leaf) — carry every descendant it
has *any* occupant for, rather than collapsing the whole thing to opaque the
moment one descendant is: the two used to be the same test, which is exactly
what made a materialized descendant of an otherwise-opaque parent
permanently unreachable the moment that parent left `peaks/` (§2.7 below).
*Checked by: property test — a subtree-kind log and a resumed log must
never call `store_leaf`, and the git backend must never synthesize a `leaf`
or child entry it was not handed.*

**A resumption's storage MUST be fresh.** `NaryMerkleLog::resume` writes
forward into a backend that carries no prior committed log of its own; a
target that already holds one (`Storage::load_log_meta` returns `Some`) is
refused before anything is written (§4.5, a named error). This is what lets
a backend implementation stay silent on the question SG11 answers below --
a touched coordinate's prior occupant, if any, is always this same log's own
(an ordinary continuing write, whose prior digests/leaf/children carry
forward per SG11), never a stale, unrelated occupant left over from
something else, because that third case is foreclosed at the door rather
than reconciled after the fact. Freshness is scoped to `storage`'s own
staging ref, never to the repository as a whole: `GitStorage`'s
`load_log_meta` answers from `observed_tip`, populated in `GitStorage::new`
from a lookup of that instance's own `staging_ref` alone, never from
scanning the object database or any other ref. A repository holding several
logs side by side under distinct staging refs therefore reports freshness
correctly per ref -- one ref's committed log is never visible through
another's `GitStorage` instance. This is exactly what makes a fork
supported: sealing a log under one ref and resuming into a brand-new ref in
that same repository is a fresh-target resume like any other, while
resuming the same seal back onto the ref that still holds the source log is
refused, whether or not that ref lives in the same repository as the
fork's target.

**[SG11]** Opacity is a property of the node, not of the log. A single log
instance MAY carry both materialized nodes (from before a resumption or
before its first subtree-kind append) and opaque nodes (from after). A
backend implementation MUST NOT infer materialization from the log's current
`meta.kind` byte; it MUST infer it from whether it was ever handed the leaf
bytes or the child structure for that specific node. *Checked by: property
test — mix flat and subtree appends where `cml` permits it, and confirm
per-node opacity matches per-node provenance, not the log-wide kind byte.*

An opaque node can never become materialized through this trait: `Storage`
has no operation that backfills a node's children after the fact. Filling a
gap from real historical data (`polydigest::fill`) is an application-level,
trustless rehydration that reads the *original* data source, not this git
backend's own object store, and is out of this layer's scope (§8).

### 2.7 Permanent reachability by decomposition (no side archive)

An earlier revision of this layer (`inherited/`, SG28/SG29 in prior
versions of this document) archived a superseded opaque peak into a side
tree the moment a later write's frontier stopped naming it, because that
write's `T(left, h)` replacement was built **opaque whenever any child it
would need to attach was not fully materialized** — so a coordinate one
level below the new peak, even a genuinely materialized one, was silently
dropped: nothing in the new tree referenced it, and the very next write that
retired its parent made it permanently unreachable. That defect (not a gap
in the archive's coverage, a gap in *what got built in the first place*) is
what an ordinary forward `append_leaf` on a resumed log exposes: its
materialized leaf sits directly beside the inherited opaque genesis frontier
in the very next merge, and the old rule would have discarded it on the
spot.

The fix removes the defect at its source instead of archiving around it:
§2.6's `hex(c, 2)` children are now wired together, all at once, gated on
every child slot having a known occupant rather than on the whole subtree
being materialized — whichever occupant this layer actually knows about
for each slot, opaque or materialized, is wired in unchanged. A coordinate
that was ever a frontier peak is
therefore *always* reachable afterward, by ordinary §2.4 descent from
whatever taller peak now covers it — ordinarily one hop, transitively many
after several merges, but never a separate lookup outside `peaks/`. Nothing
is archived, nothing is copied: a superseded coordinate's `T(left, h)`
object is reused by object id (SG18a) as a child of its new parent, exactly
like a materialized one always was. This is why a former `inherited/`
archive is not merely small now, it does not exist at all — `C(n)` keeps
SG1's original four-entry shape unconditionally, for every log, resumed or
not, flat or subtree-kind.

**[SG28]** For any coordinate `(left, h)` this layer ever built with a known
digest (via `store_leaf`, `store_node`, or `write_batch`'s `nodes`), every
later write's `T(left', h')` for any taller coordinate that comes to cover
`(left, h)` MUST carry a `hex(c, 2)` entry along the path down to it,
reusing `T(left, h)`'s own object id unchanged for as long as that
coordinate's own digest never changes again (which, once it stops being a
frontier peak, is forever — `cml::engine::carry` never re-touches a sealed
position). *Checked by: property test — comparing every coordinate a
sequence's frontier has ever named against `MemoryStorage` (which never
drops a node it was given) at every step, not just the current frontier.*

**[SG29]** A reader resolving `(alg_id, left, h)` MUST descend from the
current frontier's covering peak (§2.4) and answer from whatever
`T(left, h)` it finds there — this is now the *only* path, live or
historical (`tree_at`), and it always succeeds for a coordinate that was
ever itself a frontier peak (SG28). The one case that remains genuinely
unreconstructable is a coordinate strictly *beneath* a leaf-level opaque
node (`h = 0` with no `leaf` blob) that was never itself a peak: SG4 forbids
a height-0 opaque node from carrying anything to descend through, and no
digest was ever given for a position beneath it in the first place, so
`get_node` MUST answer `Ok(None)` and `tree_at` MUST answer a reconstruction
error naming the coordinate. *Checked by: the same property test as SG28,
extended to every historical size the sequence has passed through via
`tree_at`.*

## 3. Byte-exact encodings

Every blob this layer ever writes is one of five shapes. Multi-byte integers
are big-endian throughout, matching the encoding `storage-fjall` already
uses for the same fields (`storage-fjall/src/lib.rs:163-252`), so a
migration between backends never has to reconcile endianness.

### 3.1 `meta` (fixed 11 bytes)

| Offset | Width | Field | Value |
| --: | --: | :-- | :-- |
| 0 | 2 | arity | `k` as `u16` BE |
| 2 | 8 | count | `n` as `u64` BE |
| 10 | 1 | kind | `0x00` = flat, `0x01` = subtree (`cml::LogKind::to_byte`, `cml/src/lib.rs`) |

**[SG12]** `meta` MUST be exactly these 11 bytes in this order, with no
trailing padding, the same fixed shape for every log regardless of resume
history: there is nothing this early to stay compatible with, so no wider,
resume-carrying shape and no version byte exist to distinguish a shape that
has never had a second variant. A reader MUST reject any other length.
*Checked by: golden vector; structural length check.*

At `n == 0`, `kind` MUST always be `0x00`, never a value read off the log's
current or eventual kind. `polydigest`'s own contract already says an empty
log accepts either kind (`NaryMerkleLog::append_leaf`'s comment, "an empty
log ... accepts either kind", `polydigest/src/tree.rs:777`) — there is no
committed append at `n == 0` to bind a kind to at all, flat or subtree, so
`0x00` here is a fixed constant, not a claim about what either log's first
real append will be. Fixing it to one value (rather than, say, omitting the
byte or deriving it from some other n=0-only signal) means `C(0)` is
identical for every log with the same arity and content: two logs whose
histories diverge immediately afterward — one going flat, the other going
subtree — still commit to byte-identical `C(0)` objects, since nothing
about that later divergence exists yet at `n == 0`. `GitStorage::new`'s own
genesis default (before any ref exists) and `NaryMerkleLog::new`'s in-memory
starting `kind` are already `LogKind::Flat`/`0x00`, so this is not a new
value introduced for `tree_at(0)` alone — it is the same constant every
fresh log already starts from, now also the one `tree_at(0)`'s
reconstruction uses regardless of what the log has become by the time it is
called. *Checked by: property test — `tree_at(0)` for a log whose first
append is `append_leaf` and a log whose first append is `append_subtree`,
otherwise byte-identical (arity, empty content), MUST yield the identical
`C(0)` object id.*

### 3.2 An `epochs/hex(alg_id, 16)` blob

A sequence of `(start, end)` pairs, each 16 bytes: `start` as `u64` BE,
`end` as `u64` BE, with `end = 0xFFFF_FFFF_FFFF_FFFF` (`u64::MAX`) denoting
an open (still-active) epoch. The blob is exactly `16 * len(epochs)` bytes;
zero epochs is not a valid state (an algorithm is only ever recorded here
once registered, with at least one epoch).

**[SG13]** The epoch list committed at `epochs/hex(alg_id, 16)` inside `C(n)`
MUST equal `AlgView::epochs_at(n)` (`cml/src/engine.rs:196-217`) applied to
that algorithm's full, currently-known epoch history — never the raw,
untruncated history, and never a history frozen at some earlier write.
*Checked by: property test — decode the blob and compare against
`epochs_at(n)` computed independently.*

### 3.3 A `roots/hex(alg_id, 16)` blob

The algorithm's root digest at size `n`: exactly `Hasher::digest_len()`
bytes for that algorithm, with no framing. Present only for algorithms
active at `n` (`is_active()`, matching `NaryMerkleLog`'s own
`checkpoint_roots` filter, `polydigest/src/tree.rs:409-415`); a frozen
algorithm's terminal root is read from the `C(m)` at its freeze point `m`
instead, via `tree_at(m)` (§4.3), never re-derived at a later `n`.

**[SG14]** `roots/` MUST NOT carry an entry for an algorithm not active at
`n`. *Checked by: property test.*

### 3.4 A `digest/hex(alg_id, 16)` blob (inside any `T(left, h)`)

Exactly `Hasher::digest_len()` bytes for that algorithm: `H_a(leaf bytes)`
at `h = 0`, or the folded node digest at `h > 0`, with no framing and no
length prefix — the same raw digest bytes `Storage::store_node` and
`Storage::store_leaf`'s digest computation already produce.

**[SG15]** A digest blob's length MUST equal the writing algorithm's
`Hasher::digest_len()` at read time; a reader MUST treat a mismatched
length as corruption, mirroring `get_node_hash`'s own check
(`cml/src/engine.rs:283-291`). *Checked by: property test.*

### 3.5 A `leaf` blob

The item's raw payload bytes, verbatim, with no framing — exactly what
`Storage::store_leaf(index, data)` was called with. Present only on a
materialized `T(left, 0)` (§2.6).

**[SG16]** `leaf`'s bytes MUST be byte-identical to the argument
`store_leaf` received; this layer MUST NOT transform, compress, or frame
the payload in any way. *Checked by: golden vector; property test round-trip.*

## 4. Storage-trait mapping and additions

`polydigest::Storage` is unchanged by this backend (`polydigest/src/storage.rs:13-115`);
every method below is a mapping onto the layout in §2–§3, plus the four
git-native additions §4.2–§4.5 the trait does not and should not carry,
because they are meaningful only for a backend with a git-shaped history.

### 4.1 Read methods

`len`, `get_leaf`, `get_node`, `load_algorithm_metas`, `load_log_meta`, and
`load_checkpoint_roots` all read from the **staged tree** — the tree the
staging ref (§4.2) currently points at — via the position-lookup algorithm
of §2.4 and the decodings of §3. `is_empty` keeps the trait's default
(`len() == 0`) unchanged.

### 4.2 The staging ref and compare-and-swap writes

**[SG17]** Each `storage-git` instance owns exactly one git reference (the
**staging ref**), supplied at construction (for example
`refs/eml/storage/<name>/staging`), analogous to `storage-fjall`'s
per-instance keyspace prefix (`storage-fjall/src/lib.rs:100-157`) — this is
how two logical logs share one repository without colliding. The staging
ref's target MUST always be a tree object, `C(n)` for the instance's current
`n`; it MUST NOT be a commit. *Checked by: structural; a compiled check against the pinned tag confirms `gix`
places no kind restriction on a `RefEdit`'s target.*

**[SG18]** `store_leaf`, `store_node`, `store_algorithm_meta`, and
`write_batch` each MUST: (a) build the new `C(n')` tree object per §2–§3,
reusing unchanged children by object id rather than rewriting them; (b)
write every newly-referenced object through the object database's writer
(§5, SG22), never through a `Repository`-level convenience method; (c) move the
staging ref from the tree id this instance last observed (or require
`MustNotExist` for a fresh instance's genesis write) to the new `C(n')`, in
one `gix` reference-edit transaction; (d) treat every non-batched method as
a one-item batch through the identical compare-and-swap path, so no method
bypasses it. *Checked by: property test; a compiled check against the pinned tag confirms
`gix::Repository::edit_references` rolls back every edit in a transaction
atomically on any single precondition failure.*

**[SG19]** If the compare-and-swap precondition fails (the ref's actual
value differs from what this instance last observed), the write MUST fail
as a whole, MUST NOT move the ref, and MUST return a distinguished
**tip-moved** error — a variant of the backend's `Storage::Error` distinct
from I/O or corruption failures — rather than any other error shape. Any
object the failed attempt wrote remains unreferenced and is left for
collection (§5); it MUST NOT be reused on retry without being re-verified
present. The caller (the `polydigest` combinator) is responsible for
reloading the log from the ref's new value and retrying; this layer performs
no retry of its own. *Checked by: property test — force a concurrent writer
to move the ref between this instance's last read and its write, and assert
the tip-moved variant is returned and the ref is unmoved from the concurrent
writer's value.*

Because every `storage-git` instance is single-writer within its own
process (mirroring `storage-fjall`'s non-`Clone` `FjallStorage`,
`storage-fjall/src/lib.rs:53`), the race SG19 guards against is only ever
against another process or another instance — never against concurrent
calls on the same instance, which Rust's `&mut self` on every mutating
trait method already forecloses.

### 4.3 `tree_at(n)` — an addition beyond the trait

**[SG20]** `tree_at(n: u64) -> Result<ObjectId, Error>` MUST return `C(n)`'s
object id for any `n` from `0` to the instance's current size, inclusive.
For `n` equal to the current size, this is the staging ref's target read
directly. For any earlier `n`, it MUST be **reconstructed** — never assumed
already written as a standalone object — from: the sealed subtrees already
present (every aligned block below the current size is sealed and
unchanged, §2.4), and the current, full epoch history truncated to `n` via
`epochs_at(n)` (§3.2, SG13). If the reconstructed object is not already
present in the object database, `tree_at` MUST write it (idempotently — by
SG9's purity, a repeated build always produces the same id) before
returning its id. `tree_at` MUST NOT move the staging ref. *Checked by:
property test — `tree_at(n)` for a range of past `n` MUST match a
from-genesis rebuild's `C(n)` for the same log state.*

**Amendment — `roots/` reconstruction and `register_hasher`.** A
historical `roots/hex(alg_id,16)` entry (§3.3, SG14) is a per-algorithm
*member root*: the peak-bagging fold (`cml::mountain::bag_peaks`,
the same fold `cml::engine::compute_root` uses to produce the live root this
layer stores verbatim via `checkpoint_roots`) over that algorithm's frontier
peak digests as they stood at `n`. Unlike `meta`/`epochs`/`peaks`, this fold
is not recoverable from stored bytes alone — folding more than one peak
digest into one root is a hash operation this layer does not otherwise
perform, so reconstructing it needs the algorithm's own hash fold, not
merely its already-stored digests. This does not relax SG26: the fold runs
under a `spine::Hasher` **trait object** the caller registers per `alg_id`
via `GitStorage::register_hasher(alg_id, Box<dyn Hasher>)` — an addition
alongside `tree_at`/`open_at` — never a hash algorithm this crate names,
links against by concrete type, or assumes a digest width for; the
interface is exactly the opaque, caller-supplied shape SG26 already
requires everywhere else. A `tree_at(n)` call reconstructs `roots/hex(alg_id,16)`
correctly for every algorithm with a hasher registered this way. `tree_at`
MUST NOT return a tree other than `C(n)`: for an algorithm active at `n`
with **no** hasher registered, it MUST return an error naming the
algorithm, never `Ok` with the entry silently omitted -- omitting the entry
would turn a missing precondition into a well-formed but wrong tree that a
consumer (for example an Axios view commit) could not distinguish from the
genuine one. At `n = 0` the frontier is empty by construction (no item has
ever been appended), so no algorithm's root has ever actually been computed
by the combinator regardless of registration; `roots/` at `n = 0` is always
the empty tree, matching the checkpoint tree this layer itself writes when
an algorithm is first registered (§4, SG18: a registration alone never
supplies `checkpoint_roots`), and this one case needs no hasher and never
errors. *Checked by: property test — `tree_at(n)` for a range of past `n`,
with every registered algorithm's hasher supplied, MUST be byte-identical
to the checkpoint tree actually written at size `n`, including `roots/`;
and `tree_at(n)` for an algorithm active at `n` with no hasher registered
MUST return an error naming that algorithm, for every such `n`.*

**Amendment — a registered hasher is trusted only on stored evidence.** A
registered hasher of the wrong digest width, or of the right width but the
wrong function, MUST be rejected rather than silently folded into a
historical `roots/` entry that is then indistinguishable from a genuine
one. `tree_at` MUST check a registered hasher against digests this layer
already has on file for that algorithm before trusting it for any
historical reconstruction, and MUST return an error rather than `Ok` on a
mismatch, and draws on two forms of evidence, both computed over the
*current*, live frontier regardless of which `n` is being reconstructed.
First, bottom-up recomputation: a currently active, fully-covered node's own
digest, recomputed via `spine::nary_mr` (`Hasher::leaf` at the leaves, the
same promotion-and-collapse fold `cml::engine::carry` itself applies at each
merge -- never `Hasher::node` called directly, which would reject a correct
hasher wherever eml's own canonicalization has collapsed equal children to
their shared value) and compared against the digest already stored at that
exact coordinate. A peak the algorithm is not fully active over supplies no
evidence either way -- it is simply not this algorithm's node to recompute,
never a reason to distrust the hasher; a peak the algorithm fully owns but
that turns out opaque is the genuine absence of evidence this check must
not paper over. Second, frontier folding: where the current frontier
carries two or more peaks, folding their stored digests via `bag_peaks`
(the same fold `cml::engine::compute_root` uses) and comparing the result
against the algorithm's already-stored `roots/` entry is evidence enough to
catch a wrong function even when nothing can be recomputed bottom-up
(`cml::mountain::bag_peaks` promotes a lone peak to itself, so a
single-peak frontier never actually exercises a wrong hasher through this
path -- this is why it takes two or more). Either form of demonstrated
wrongness MUST be rejected unconditionally, regardless of which `n` is being
reconstructed: a hasher already proven wrong is never safe to fold anything
with. An algorithm with a fully-owned peak that turns out opaque, and fewer
than two frontier peaks to fall back on, has no evidence either way -- and
MUST NOT be silently trusted -- but only where reconstructing the requested
`n` would actually need that trust: a fold is only ever needed to combine
two or more of `n`'s *own* frontier peaks, so this refusal MUST NOT fire for
`n` equal to the current size (served as the staging tip, needing no fold at
all) nor for a target frontier of zero or one peak (`bag_peaks` promotes a
lone peak to itself, and an empty frontier has no root to fold, mirroring
the `n = 0` case above); it MUST still fire wherever reconstructing `n`
genuinely needs a fold across two or more of its own peaks and no evidence
exists anywhere to trust the hasher for it. *Checked by: property test — a
hasher of a different digest width, and a hasher of the same width but a
different function, registered for an algorithm with real,
correctly-computed digests already stored, MUST both cause `tree_at` to
return an error rather than `Ok`, including where every node is opaque and
only a multi-peak frontier fold supplies the evidence; and a fork resumed at
a single-peak size, with the correct hasher registered, MUST succeed at
`tree_at(0)` and at `tree_at` of the current size, never refused for lack of
evidence a query needing no fold was never going to use.*

The rejected alternative — persisting each root as it is computed, rather
than folding it back from stored peaks on demand — does not compose with
SG9/SG18: a `write_batch` carry can seal several sizes' worth of internal
merges in one call (SG18's frontier carry, §2.4), and most of the
intermediate sizes it passes through are never themselves written as a
standalone `C(m)` object at all (only the batch's final size is). A
size-indexed root history would therefore need to persist a value for
sizes this layer never otherwise materializes as anything, which is a new,
unbounded, size-indexed structure outside §2.1's fixed four-entry schema —
exactly the "size-indexed root history" §2.5 already names as something
this layer's object model has no room for. Folding on demand from data
this layer already reconstructs needs no such structure and costs nothing
when a caller never calls `tree_at` for a historical `n`.

### 4.4 `open_at(tree)` — an addition beyond the trait

**[SG21]** `open_at(tree: ObjectId) -> Result<impl ReadOnlyView, Error>` MUST
return a read-only view exposing `get_leaf`, `get_node`,
`load_algorithm_metas`, and `load_checkpoint_roots` against the supplied
tree object, decoded exactly as §2–§3 specify, independent of this
instance's own staging ref and current size. It MUST NOT accept or perform
any mutation. Reading through a view returned by `open_at(tree_at(m))` for
some past `m` MUST yield the same leaf and node values `get_leaf`/`get_node`
returned when the log was actually at size `m` (durable-witness parity with
`cml`'s own MMR guarantee that a proof generated before an append remains
valid after it, `docs/architecture.md`, "Conformance and durability property
tests"). *Checked by: property test.*

### 4.5 The tip-moved error

Specified as part of SG19; repeated here because it is one of the named
additions (§4.2–§4.4 and this section: `tree_at`, `open_at`,
`register_hasher`, and the tip-moved error itself). It MUST
be introspectable by the caller (a distinguishable
variant or an `is_tip_moved()`-style predicate), never conflated with
"object not found" or "corrupted", since the caller's correct response
(reload and retry) differs from its response to either of those.

## 5. Garbage-collection safety

The threat: git's own garbage collector reclaims any object that is both
unreachable from any ref and older than its prune grace period. A write in
progress here creates objects before the staging ref is moved to reference
them, so a concurrently running `gc` can — absent the rules below — delete
an object this layer is about to depend on.

**[SG22]** `gix::Repository`'s convenience write methods (`write_blob`,
`write_object`, and everything built on `write_object_inner`) hash the
payload in memory, find the object already exists, and **return without
writing or touching the existing file at all** — confirmed by compiling a check against the pinned
tag directly against the source (`gix/src/repository/object.rs:262, 293, 319`). Because `gix` has no dedicated "freshen" API at this tag (a
project-wide search for `freshen`/`touch_object`/`refresh_object` across
`gix` and `gix-odb` returns nothing), an object that already exists,
unreferenced, and past the grace period would be silently left exactly as
old as it was — inviting a concurrent prune to remove it before this
layer's own reference edit lands. This layer therefore MUST write every
object through the object database handle's `write_buf_with_known_id`
(`repo.objects`, the `OdbHandle`; `gix-odb/src/store_impls/dynamic/write.rs:47-64`),
never through `Repository`'s shortcut methods — that call always rebuilds a
fresh compressed tempfile and renames it onto the destination, refreshing
its mtime as an ordinary consequence of the rename, a fact compiled and
measured directly against the pinned tag rather than assumed from
documentation. *Checked by: a compiled check against the pinned tag (already
run during this workstream's survey); the backend implementation MUST cite
this exact call in its own write path, checked by code review against this
constraint at implementation time.*

**[SG23]** After every batch, before returning success to the caller, this
layer MUST verify that every object the batch newly references is still
present (a header read, not a full read), and MUST re-write and re-verify
any that are found missing before considering the write durable. This
follows SG22: freshening resets an object's age, but a prune with an
aggressive expiry can still fall inside the narrow window between the
freshening write and the reference edit that makes the object reachable.
*Checked by: property test simulating a missing object post-write; the
residual named in SG24 is what this rule cannot close.*

**[SG24] Residual gap, named rather than closed.** A `git gc` or `git prune`
invoked with an immediate expiry (`--prune=now` or equivalent) concurrently
with an in-flight write can still race the window between SG22's freshening
write and SG18's reference edit, because freshening resets an object's
*age*, not its *reachability* — reachability only exists once the ref moves.
This is not a defect this layer's object model can close; it is the same
constraint git documents for its own concurrent writers. **Operators MUST
NOT run an immediate-expiry prune against a repository storage-git is
actively writing to**; git's default (non-zero) prune grace period is
sufficient margin under SG22–SG23's freshening and re-verification, and is
the assumed operating condition. *Checked by: none — this is an
operational constraint on deployment, not a property this crate's test
suite can exercise; it MUST be stated in the crate's own operational
documentation, not silently assumed.*

**[SG25]** The staging ref's move (SG18c) is the sole commit point. A crash
at any point **before** that reference edit lands leaves only unreferenced
objects — the exact "no partial state" contract `Storage::write_batch`
already requires (`polydigest/src/storage.rs:96-98`) — and a crash **after**
it lands leaves a fully valid `C(n')` with everything SG22–SG23 required
already reachable. There is no partial-batch state a reader can observe
through the staging ref. *Checked by: property test — kill the process at
each of several injection points around a write and assert the ref, on
restart, is either at the old or the new tree, never anything else.*

## 6. Algorithm parametricity — no hash hardcoded

**[SG26]** No function in this crate MUST name a specific hash algorithm,
reference a specific hashing library, or assume a specific digest width.
Every digest this layer writes or reads is caller-supplied bytes keyed by a
caller-supplied `alg_id: u64`; the only width this layer ever consults is
whatever `Hasher::digest_len()` reports for that algorithm at the moment of
the read that needs it (SG15). *Checked by: source audit at implementation
time (a grep for known hash-library or hash-function identifiers in this
crate's source is expected to find none) and by property tests parametrized
over more than one `Hasher` implementation with different digest widths, so
a width assumption anywhere would fail at least one width's tests.*

**[SG27]** This layer MUST work unmodified against a repository under
either git object-hash format (SHA-1 or SHA-256), by querying
`Repository::object_hash()` at open time (confirmed queryable and
correctly re-detected from an existing repository, not merely from creation
options, by a compiled check against the pinned tag) rather than assuming one. Git's own
object-hash format carries no security weight in this design ("Status and
scope", above): a
verifier's trust rests on rehashing bytes actually read against the
caller's committed digest, so a colliding git object id can, at worst,
cause a stale read to be detected as a mismatch — never cause a forged
digest to be accepted. Preferring a SHA-256 repository is therefore a
caller's operational choice (stronger collision resistance on git's own
pointers, and a sound key for an optional ingest-side digest cache outside
this layer's scope), never a requirement this layer imposes or assumes.
*Checked by: the crate's test suite MUST run its full property-test suite
against a repository of each object-hash format.*

## 7. Verification and test-invariant mapping

Every `SG<n>` constraint above names its check inline. Summarized, a
`storage-git` implementation's test suite MUST include, alongside
`storage-fjall`'s existing pattern (`storage-fjall/tests/proptests.rs`,
`storage-fjall/tests/integration.rs`) and `polydigest`'s own suite
(`polydigest/tests/`):

| Constraint group | Test shape |
| :-- | :-- |
| SG1–SG8 (layout, position lookup) | Property tests comparing this backend's reads against `MemoryStorage` over the same operation sequence, for a range of `k` and `n` |
| SG7 (pre-sorted entries) | A release-mode unit test, since the failure mode is compiled out of `debug_assert!` |
| SG9, SG20 (purity, `tree_at`) | Property tests over reordered-but-equivalent operation sequences and over historical `n` |
| SG10–SG11 (opacity) | Property tests mixing flat, subtree, and resumed logs |
| SG28–SG29 (permanent reachability by decomposition) | Property tests over fork lifecycles (seal, resume, forward leaf and subtree appends, reopen), comparing every coordinate and every historical size the sequence has ever named against `MemoryStorage` |
| SG12–SG16 (byte-exact encodings) | Golden vectors: fixed `(k, leaves, algorithms)` inputs with pinned expected object ids, one per supported object-hash format |
| SG17–SG19, SG25 (staging ref, CAS, tip-moved, crash safety) | Property/integration tests using two `storage-git` instances against one bare repository, one racing the other's write |
| SG21 (`open_at`) | Durability property test mirroring `docs/architecture.md`'s existing MMR durable-witness test pattern |
| SG22–SG24 (GC safety) | A test asserting the exact `write_buf_with_known_id` call path is used (SG22); a simulated missing-object recovery test (SG23); SG24 is documented, not tested |
| SG26–SG27 (algorithm and object-hash parametricity) | The full property-test suite run parametrized over at least two `Hasher` implementations of different digest widths and over both git object-hash formats |

This is the CONNECT mapping the specification workflow requires: every
normative constraint above has a named, deterministic evaluator. None is
left as prose alone.

## 8. Explicitly out of scope

Named here so absence reads as a boundary, not a gap.

- **Checkpoint commits, parents, and retention.** Wrapping `tree_at(n)` in a
  commit, the checkpoint ref's own forward-only compare-and-swap, an
  application's retention parents (holding a content or view commit alive
  against garbage collection), and companion ref edits are the checkpoint
  library's responsibility, one layer up. This layer's staging ref is not
  that checkpoint ref, and its compare-and-swap (SG17–SG19) is not a
  substitute for the checkpoint chain's.
- **Content-tree ingestion and its Merkle commitment.** Computing a
  content commitment over an arbitrary, externally supplied git tree (for
  example a working directory's real files) — including the choice between
  a flat recursive digest and a balanced per-directory tree, and the
  handling of gitlink entries — is a separate concern, consumed by a
  content-mirror library that depends on this layer for nothing but a place
  to (optionally) store the blobs it walks. No byte-exact encoding for that
  mirror is specified here.
- **Ref naming policy, checkpoint cadence, and commit metadata** are
  application concerns by design ("Status and scope", above); this layer
  accepts a caller-supplied
  ref name (SG17) and imposes no policy on how often a caller checkpoints.
- **Which hash algorithms are actually registered**, and how many, is a
  caller and application decision (§6); this specification fixes none.
