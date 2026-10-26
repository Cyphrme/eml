# SPEC: storage-git — the git storage backend

## Status and scope

This is the normative specification for `storage-git`, a backend crate that
implements `polydigest`'s `Storage` trait (`polydigest/src/storage.rs`) over a
git object database reached through `gix`, pinned to `gix = "=0.87.1"`. It is
the first of three layers a larger git-backed storage design decomposes into:

1. **This layer.** Raw positional storage: leaves and sealed node digests,
   laid out as git objects, behind the unmodified `Storage` trait plus a small
   set of git-native additions (compare-and-swap writes and a tip-tree
   accessor). No commits. No refs other than one staging ref per log
   instance. No application policy. This layer keeps the **complete**
   checkpoint tree behind that ref, forever; it never renders or
   reconstructs a tree for a past size.
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
  algorithm; this layer never sees `H` and never assumes or checks it.
- `k` — the log's arity, `2 <= k <= 256` (`spine::ARITY_RANGE`,
  `spine/src/topology.rs:27`). Persisted in `meta` (§3.1) but otherwise
  irrelevant to this layer's own object layout (§2), which places every node
  and leaf purely by key.
- `n` — the log's global size: the number of appended items (`polydigest`'s
  `count`, `Storage::len()`).
- `alg_id` — a `u64` algorithm identifier, opaque to this layer.
- `T(left, h)` — the sealed perfect `k`-ary subtree covering item indices
  `[left, left + k^h)`. `T(left, 0)` is a single item's node; its digest for
  algorithm `a` is the opaque bytes a [`polydigest::WriteOp`]'s `nodes` field
  carried for `(a, left, h)`, with no further internal structure (§2.2).
- `C(n)` — the checkpoint tree: the complete, self-describing git tree
  recording the log's state at size `n` (§2.1).
- `trimmed(x)` — the `byte1-be-trim` key path scheme (§2.2): a sequence of
  path segments derived purely from the `u64` `x`, used to place every node
  and leaf at a path derived only from its own key.

Every constraint below is tagged `SG<n>` and states how it is checked. A tag
of **property test** or **golden vector** names a check this crate's test
suite MUST carry once implemented; **structural** names a fact enforced by
the object layout itself (violating it produces an object no reader can
parse as this layout, not merely a wrong one); **compiled probe** cites a
`gix` behavior already confirmed by compiling against the pinned tag, not
merely read from source or documentation.

## 2. The git object layout

### 2.1 The checkpoint tree — key-derived placement

Every node and leaf lives at a git tree path derived **only** from its own
key. There is no peak-and-children hierarchy, no decomposition of a taller
coordinate into its parts, and no materialized-versus-opaque distinction — a
write adds exactly the keys it is given, with nothing wired or carried
forward by decision. `meta`/`epochs` are the one exception: small,
non-key-addressed metadata that is genuinely mutated (not merely appended
to) on each write.

**Design rationale.** This layout replaces an earlier peak-and-children
scheme that wired each write into a decomposition of taller coordinates and
had to re-decide, on every write, whether a coordinate was materialized or
opaque; a wrong decision there silently dropped a materialized descendant
the moment its parent stopped being a frontier peak (§2.6 recounts the
defect this was built to eliminate structurally rather than patch). Two
placement schemes were measured and rejected before settling on this one:

- **A single flat directory per key space** (one `leaves/`/`nodes/` tree with
  every key as a direct sibling) is unbounded: the same directory object is
  fully re-read, re-sorted, and re-serialized on every write, so its
  serialized size — and therefore the per-write cost — grows linearly with
  the log's size forever.
- **Byte-fanout in little-endian order** (least-significant byte first)
  bounds directory width the same way big-endian fanout does, but places
  each key's near-always-zero high-order bytes at the leaves rather than the
  root. Those bytes are exactly the ones many keys share, so big-endian
  fanout lets one ancestor object cover every key with the same high-order
  prefix (git's own content addressing deduplicates it once), while
  little-endian fanout gives every key its own private copy of an otherwise
  identical ancestor chain — measured at roughly 7x more standing, `git
  gc`-immune objects for the same logical content in an exploratory
  prototype of this design.

The scheme this layer implements — one-byte big-endian fanout with a key's
leading zero bytes trimmed behind an explicit length segment (`trimmed`,
§2.2) — keeps the bounded-width property (SG2: no tree object exceeds 256
entries at any level) and the ancestor-sharing property of big-endian order,
while keeping a small key's path shallow instead of paying the full 8-level
depth unconditionally. The accepted cost, disclosed rather than hidden: a
key's full path can be up to 8 levels deep, so a single write touches more
objects, and orphans more superseded ancestors between `gc` runs, than the
flat or peak-wired alternatives would. That cost buys the elimination of
peak/child wiring entirely — SG2/SG3 hold by construction (a key's path is a
pure function of the key alone), not by an ordering or decomposition
invariant a future change could violate — and it is why every tree this
layer writes is assembled through one `gix::object::tree::Editor` session
per `apply` call (SG7) rather than one independent read-modify-write chain
per key: batching the whole call's edits into a single editor session is
what keeps the deeper path's per-write object count from also multiplying
the number of intermediate tree rewrites.

```
C(n)                          tree
  meta                        blob    §3.1
  epochs/                     tree    one blob per ever-registered algorithm
    hex(alg_id, 16)           blob    §3.2
  nodes/                      tree    every sealed node digest, by key
    hex(alg_id, 16)/          tree
      hex(h, 2)/              tree
        trimmed(left)         blob    §2.2, §3.3
  leaves/                     tree    every leaf, by key
    trimmed(index)            blob    §2.2, §3.4
```

**[SG1]** `C(n)`'s top-level entries MUST be an exhaustive subset of exactly
`{meta, epochs, nodes, leaves}` — `meta` present always;
`epochs`/`nodes`/`leaves` present once anything has ever been written under
them. No other top-level entry MUST ever exist — in particular, no `roots`
entry ever exists, at any `n`: a per-algorithm root is an index over data
this layer already stores under `nodes/`, and an index over this layer's
own data belongs at the application layer, not here (head's ruling,
2026-09-17). *Checked by: structural — an exhaustive allow-list walk of
`C(n)`'s direct entries.*

**[SG2]** A node's digest for algorithm `a` at `(left, h)` lives at exactly
`nodes/hex(a,16)/hex(h,2)/trimmed(left)`; a leaf's raw bytes at exactly
`leaves/trimmed(index)`. `trimmed(x)` (`byte1-be-trim`,
`src/layout.rs::trimmed_key_segments`) strips `x`'s leading zero bytes,
prepends a one-ASCII-digit length segment (`1..=8`, the count of remaining
significant bytes), and renders each remaining byte as its own
two-lowercase-hex-digit segment, most-significant byte first; `x == 0` is one
significant (zero) byte, never zero segments. Distinct keys always produce
distinct segment sequences — the length segment keeps two keys of different
significant-byte-length from ever sharing a directory, and fixed-width
hex-pair segments keep two keys of the same length from ever sharing one
once their bytes differ — so no tree object this scheme builds under
`nodes/` or `leaves/` ever exceeds 256 entries (one byte's worth of fan-out
at any single level). *Checked by: property test — every scheme-generated path is
injective over a representative key set (`tests/key_derived_layout.rs`'s
`trimmed_key_segments_tests`); the exhaustive-set-equality check in SG3
below empirically confirms the 256-entry bound.*

**[SG3]** For a driven operation sequence, the exact set of paths under
`nodes/` (respectively `leaves/`) MUST equal the exact set of
`trimmed`-derived paths for
every `(alg_id, left, height)` node coordinate (respectively every leaf
`index`) an independent, non-git reference implementation (`MemoryStorage`)
was ever given for that sequence — catching a missing entry, a stray entry,
and a misplaced entry all at once, since any of the three breaks set
equality. This subsumes the retired peak-and-children layout's SG3/SG4
concerns (an algorithm's digest never leaking into the wrong range, a node's
materialized-vs-opaque shape) structurally: since `alg_id` is itself a path
segment, a different algorithm's digest is a wholly different path, never a
sibling entry inside a shared subtree a purity bug could pollute; and since
every coordinate lives at its own permanent, independent key, there is no
decomposition step left to build a node's shape incorrectly. *Checked by:
property test comparing git's own enumerated key set (`tests/
key_derived_layout.rs`, `tests/reverse_completeness.rs`) against
`MemoryStorage`'s, both directions (forward: nothing git holds is missing
from memory's set; reverse: git holds nothing memory doesn't), across the
full operation vocabulary (append, add/remove/resume algorithm, fork,
reopen, gc) and arities 2 through 4.*

### 2.2 A node or leaf's stored value

A node's digest and a leaf's payload are each stored as a single blob at
their own key path (§2.1) — no further internal structure, no wrapping tree,
no per-algorithm subtree (an algorithm's digest is already isolated by its
own `hex(alg_id,16)` path segment). This is a direct simplification of the
retired peak-and-children layout's `T(left, h)` shape (a `digest/` subtree
keyed by algorithm, plus an optional `leaf`/`hex(c,2)` children): the
key-derived layout needs neither, since every fact this layer stores is
already addressed by its own complete key.

This layer does not interpret or validate which algorithms *should* have a
digest at a given coordinate (the retired layout's SG3 active-range
enforcement) — it stores exactly the digests a `WriteOp`'s `nodes` field was
given, at exactly their keys, and nothing more. Whether an absent key means
"never given" or "corruption" is a question for the caller's own epoch
tracking (`polydigest`/`cml`), not something this storage layer's object
model encodes or enforces.

### 2.3 Entry modes and canonical order

**[SG5]** Every blob entry (`meta`, an `epochs`/`nodes`/`leaves`
leaf) MUST use mode `100644` (regular, non-executable). Every tree entry
(`epochs`, `nodes`, `leaves`, and every intermediate
`hex(alg_id,16)`/`hex(h,2)`/length-segment directory `trimmed(x)` builds)
MUST use mode `40000`. Nothing this layer writes is
ever a symlink or a gitlink. *Checked by: structural; `gix::objs::tree::
EntryKind::{Blob,Tree}` already normalize to exactly these two canonical
mode strings (`gix-object/src/tree/mod.rs`, confirmed by compiling a check
against the pinned tag).*

**[SG6]** The four top-level literals (`meta`, `epochs`, `nodes`,
`leaves`) are mutually distinct and never sit as siblings of a hex- or
`trimmed`-encoded entry at the same tree level (`epochs`/`nodes`/
`leaves` hold only key-fanned-out or `hex(alg_id,16)`-named subtrees;
`meta`/`epochs` never coexist with a `trimmed`-keyed sibling) —
unlike the retired peak-and-children layout, where literal names like
`leaf`/`digest` had to avoid looking like a hex string themselves because
they sat beside `hex(alg_id,16)`-named siblings, no such ambiguity is
possible here by construction. Every sibling group within one
`nodes/`/`leaves` bucket is a `trimmed`-derived length-digit or hex-pair
segment (SG2's injectivity), never mixed with a literal name. *Checked by:
structural — the four top-level literals checked pairwise-distinct
(`src/layout.rs`'s own unit test), plus SG2's injectivity property.*

**[SG7]** Every tree object this layer writes is assembled through
`gix::object::tree::Editor` (`src/build.rs::apply`, one editor session per
`apply` call), which maintains each tree's entries in git's canonical
sorted order internally as `upsert`/`remove` calls are applied — this layer
never hand-assembles or hand-sorts a `Tree`'s `entries` itself.
*Checked by: structural — the same acceptance walk SG5 uses also confirms
every sibling group in a real written tree is canonically sorted
(`tests/acceptance_layout.rs::sg6_sg7_sibling_entries_are_canonically_sorted`).*

### 2.4 Position lookup

**[SG8]** To read item `i`, or a node digest at `(alg_id, left, height)`,
resolve the derived key path (§2.2) directly under `leaves/` (respectively
`nodes/hex(alg_id,16)/hex(height,2)`) — no frontier computation, no descent, no
arity dependence at read time. A path that does not resolve means the key
was never written: `get_node` answers `Ok(None)`; `get_leaf` answers
`Err(NotFound)`. *Checked by: property test — for every valid `(n, i)` a
driven sequence reaches, the resolved value MUST match an independent,
non-git reference implementation's (`MemoryStorage`) value for the same
key.*

### 2.5 Purity

**[SG9]** `C(n)`'s object id (per object-hash format) MUST be a pure
function of exactly: `k`, the item sequence `0..n`, and the **currently
known** epoch history of every registered algorithm truncated to `n`
(`cml::engine::AlgView::epochs_at`, `cml/src/engine.rs:196-217`) — a log's
kind is never part of that function at all, since it is derived from
content rather than stored (§3.1). It MUST NOT depend on insertion
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
underlying epoch history to `n` via `epochs_at`. This layer only ever holds
one `C(n)` at a time -- the current size's, behind the staging ref (§4.2) --
and never builds a `C(m)` for `m < n` on its own account; any intermediate
object a partial write left behind is simply unreferenced and eligible for
collection (§5). A past logical state is read by wrapping an earlier `C(m)`
in a commit before this layer's own tree moves past it (the checkpoint
library, out of scope here, §8) or by `eml` reading directly over the nodes
the current, complete `C(n)` still contains (§2.2).

### 2.6 Retired: materialized/opaque nodes and permanent reachability

A prior peak-and-children layout distinguished a **materialized** node
(built down to real payload bytes or real children) from an **opaque** one
(known only by digest), and had to re-decide, on every write, which shape a
taller coordinate's replacement should take -- an earlier revision of that
decision (built opaque whenever *any* child it needed to attach was not
fully materialized) silently dropped a materialized descendant the moment
its parent stopped being a frontier peak, which an `inherited/` archive and
then a corrected all-or-nothing-per-slot decomposition rule (former SG10,
SG11, SG28, SG29) were built to fix.

The key-derived layout (§2.1) removes the defect at its root instead of
patching around it: every coordinate this layer is ever given lives at its own permanent,
independent key path (§2.2), forever, so there is no taller coordinate to
decompose, no per-write decision about a node's shape, and no reachability
argument to make -- a key that was ever written stays exactly where it was
written, for the life of the log. `resume`'s freshness requirement
(a nonzero `Storage::append_count` or a non-empty `load_algorithm_metas`
refuses a resumption target before anything is written) is unchanged and
still matters for the same
reason it always did: it forecloses the one case a backend would otherwise
have to reconcile a touched coordinate's prior occupant against -- a stale,
unrelated value left over from something else. With per-key storage,
"whatever a coordinate held before" is simply "whatever this same key held
before," never ambiguous.

## 3. Byte-exact encodings

Every blob this layer ever writes is one of four shapes. Multi-byte integers
are big-endian throughout, matching the encoding `storage-fjall` already
uses for the same fields (`storage-fjall/src/lib.rs:163-252`), so a
migration between backends never has to reconcile endianness.

### 3.1 `meta` (fixed 10 bytes)

| Offset | Width | Field | Value |
| --: | --: | :-- | :-- |
| 0 | 2 | arity | `k` as `u16` BE |
| 2 | 8 | count | `n` as `u64` BE |

**[SG12]** `meta` MUST be exactly these 10 bytes in this order, with no
trailing padding, the same fixed shape for every log regardless of resume
history: there is nothing this early to stay compatible with, so no wider,
resume-carrying shape and no version byte exist to distinguish a shape that
has never had a second variant. A reader MUST reject any other length.
*Checked by: golden vector; structural length check.*

**Kind derivation.** `meta` carries no kind field at all: a log's kind
(flat vs. subtree) is never persisted anywhere in `C(n)` — it is derived
from content, the same way `polydigest::Storage::len`'s own doc comment
specifies for every backend. `GitStorage::metadata()`/
`GitReadOnlyView::metadata()` (§4.6) derive it as `LogKind::Flat` whenever
`n == 0` (either kind is equally valid there — there is no committed append
yet to bind a kind to) or whenever `leaves/` has ever gained an entry;
`LogKind::Subtree` otherwise (a nonzero `n` with no `leaves/` entry — a
resumed or subtree-appended-from-genesis log). Since `meta` never encodes
kind, two logs whose histories diverge immediately after `n == 0` — one
going flat, the other going subtree — commit to byte-identical `C(0)`
objects as a structural consequence, not a canonicalized special case.
*Checked by: property test — a genuine `C(0)` write for a log whose first
append will be `append_leaf` and one whose first append will be
`append_subtree`, otherwise byte-identical (arity, empty content), MUST
yield the identical `C(0)` object id.*

### 3.2 An `epochs/hex(alg_id, 16)` blob

A sequence of `(start, end)` pairs, each 16 bytes: `start` as `u64` BE,
`end` as `u64` BE, with `end = 0xFFFF_FFFF_FFFF_FFFF` (`u64::MAX`) denoting
an open (still-active) epoch. The blob is exactly `16 * len(epochs)` bytes;
zero epochs is not a valid state (an algorithm is only ever recorded here
once registered, with at least one epoch).

**[SG13]** The epoch list committed at `epochs/hex(alg_id, 16)` inside
`C(n)` MUST equal `AlgView::epochs_at(n)` (`cml/src/engine.rs:196-217`)
applied to that algorithm's full, currently-known epoch history — never the
raw, untruncated history, and never a history frozen at some earlier
write. Every currently-registered algorithm's `epochs/` entry is
re-projected against the batch's own final `n` and rewritten on every
`apply` call, whether that call's own ops named the algorithm or not, so an
unchanged blob is freshened (§5, SG22) exactly as a touched one is.
*Checked by: property test — decode the blob and compare against
`epochs_at(n)` computed independently.*

### 3.3 A node's blob (`nodes/hex(alg_id,16)/hex(height,2)/trimmed(left)`)

The opaque bytes a `WriteOp`'s `nodes` field carried for that key, stored
verbatim with no framing and no length prefix. This layer assigns them no
width or format: for a caller whose node is a bare digest they are
`H_a(leaf bytes)` at `height = 0` or the folded node digest at
`height > 0`, but a caller may equally store longer, variable-length nodes
(for example a digest together with a summary). Since `alg_id` is itself the blob's own path
prefix (§2.1, §2.2), there is no wrapping `digest/` subtree left to key by
algorithm the way the retired layout needed.

**[SG15]** A node blob MUST be stored and returned verbatim, exactly as a
leaf blob is (§3.4): `get_node` returns the bytes the `WriteOp` carried, of
whatever length, and this layer MUST NOT reject, truncate or pad a node for
its length. Any width or format check (for example that a node is exactly
`Hasher::digest_len()` bytes, as `cml/src/engine.rs:283-291`'s
`get_node_hash` checks) belongs to the layer that holds the `Hasher` or
knows the node format; this layer holds neither (SG26). *Checked by: the
differential tests' `get_node` parity with `MemoryStorage`
(`storage-git/tests/differential.rs`), which round-trips hasher-produced
node bytes; no test stores nodes of other lengths, and a width check is
unchecked at this layer because none exists here.*

### 3.4 A leaf's blob (`leaves/trimmed(index)`)

The item's raw payload bytes, verbatim, with no framing — exactly what a
`WriteOp::AppendLeaf`'s `data` field was called with. Present iff this
layer was ever given that leaf's own bytes (an `AppendLeaf` op's `data`
argument); a subtree-kind append (`AppendSubtree`) commits only a digest,
never raw payload bytes, so it never creates a `leaves/` entry.

**[SG16]** A leaf's blob MUST be byte-identical to the argument
`WriteOp::AppendLeaf::data` carried; this layer MUST NOT transform,
compress, or frame the payload in any way. *Checked by: golden vector;
property test round-trip.*

## 4. Storage-trait mapping and additions

`polydigest::Storage` is unchanged by this backend (`polydigest/src/storage.rs`);
every method below is a mapping onto the layout in §2–§3, plus the git-native
additions §4.2–§4.6 the trait does not and should not carry, because they
are meaningful only for a backend with a git-shaped history.

### 4.1 Read methods

`len`, `get_leaf`, `get_node`, `load_algorithm_metas`, and `append_count`
all read from the **staged tree** — the tree the
staging ref (§4.2) currently points at — via the position-lookup algorithm
of §2.4 and the decodings of §3. `len` reports `0` for a subtree-kind log
regardless of its nonzero `append_count` (§3.1's kind derivation); `is_empty`
keeps the trait's default (`len() == 0`) unchanged.

### 4.2 The staging ref and compare-and-swap writes

**[SG17]** Each `storage-git` instance owns exactly one git reference (the
**staging ref**), supplied at construction (for example
`refs/eml/storage/<name>/staging`), analogous to `storage-fjall`'s
per-instance keyspace prefix (`storage-fjall/src/lib.rs:100-157`) — this is
how two logical logs share one repository without colliding. The staging
ref's target MUST always be a tree object, `C(n)` for the instance's current
`n`; it MUST NOT be a commit. *Checked by: structural; a compiled check against the pinned tag confirms `gix`
places no kind restriction on a `RefEdit`'s target.*

**[SG18]** `Storage::apply`, given any batch of one or more
[`polydigest::WriteOp`]s, MUST: (a) build the new `C(n')` tree object per
§2–§3 through exactly one batched `gix::object::tree::Editor` session
covering every key the batch touches, never one independent
read-modify-write chain per key — an ancestor path touched by more than one
key in the same call is written to the object database exactly once, on
that session's single final `write()`; (b) write every newly-referenced
object through the object database's writer (§5, SG22), never through a
`Repository`-level convenience method; (c) move the staging ref from the
tree id this instance last observed (or require `MustNotExist` for a fresh
instance's genesis write) to the new `C(n')`, in one `gix` reference-edit
transaction (§4.2's CAS, SG19/SG19a); (d) reject, without writing anything,
an `AppendLeaf`/`AppendSubtree` op whose `at` is not the current count, an
`AddAlgorithm`/`SeedFrontier` op naming an already-registered algorithm, or
a `RemoveAlgorithm`/`ResumeAlgorithm` op naming one that is not registered
— returning the distinguished `InvalidOperation` error, never panicking
(§4.5). *Checked by: property test; a compiled check against the pinned tag
confirms `gix::Repository::edit_references` rolls back every edit in a
transaction atomically on any single precondition failure.*

**[SG19]** `cas()` MUST classify an `edit_reference` failure by which
`gix_ref` transaction variant produced it, not by "any `Err`" (§8's prior
text collapsed every failure shape into `TipMoved`, which this classification
replaces): only `gix_ref::file::transaction::prepare::Error::
ReferenceOutOfDate`/`MustNotExist`/`MustExist` — the variants a transaction
reaches only by actually comparing the ref's current value against the
precondition and finding a difference — are a genuine compare-mismatch. For
one of these, the write MUST fail as a whole, MUST NOT move the ref, and
MUST return the distinguished **tip-moved** error (§4.5) — never retried
internally: deciding what to write in light of someone else's real change is
the caller's job. Any object the failed attempt wrote remains unreferenced
and is left for collection (§5); it MUST NOT be reused on retry without
being re-verified present. The caller (the `polydigest` combinator) is
responsible for reloading the log from the ref's new value and retrying.
*Checked by: property test — force a concurrent writer to move the ref
between this instance's last read and its write, and assert the tip-moved
variant is returned and the ref is unmoved from the concurrent writer's
value.*

**[SG19a]** Every other `edit_reference` failure shape (a lock a concurrent
`git gc`/`pack-refs` briefly holds, an I/O error, a packed-refs preparation
failure, or any `gix_ref::file::transaction::commit::Error` variant, which
has no mismatch case at all) never reached the point of comparing a value,
so it is safe to retry the identical edit internally: `cas()` MUST retry
such a failure, bounded by `RETRY_BOUND` (2 seconds, `src/lib.rs`) measured
from the first attempt. If the condition clears within that bound, the
write MUST succeed exactly as if no failure had occurred. If it has not
cleared once the bound is reached, `cas()` MUST give up and return the
distinguished **transient** error (§4.5) — never `TipMoved` (nothing was
ever compared) and never retried past the bound (an operator's `git gc`/
`pack-refs` that never releases its lock, or a genuinely broken repository,
must fail observably rather than hang the caller forever). *Checked by:
property test — a forced lock-contention failure (pre-created lock file)
returns the transient variant, never `TipMoved`, at both genesis and a
populated ref; a lock released well within the bound lets the write
succeed; a lock held for the whole test forces the bound to be hit and the
write to return within a generous external ceiling, never hang.*

Because every `storage-git` instance is single-writer within its own
process (mirroring `storage-fjall`'s non-`Clone` `FjallStorage`,
`storage-fjall/src/lib.rs:53`), the race SG19/SG19a guards against is only
ever against another process, another instance, or git's own housekeeping —
never against concurrent calls on the same instance, which Rust's `&mut
self` on every mutating trait method already forecloses.

### 4.3 `tip_tree()` — an addition beyond the trait

**[SG20]** `tip_tree() -> Option<ObjectId>` MUST return the tree this
instance last wrote or observed — `Some(C(n))` for the instance's current
size `n`, or `None` for a fresh instance whose staging ref has never been
written (genesis) — never a fresh re-read of the staging ref's own live
value (a concurrent writer may have moved it since this instance last
looked; this instance learns that only on its own next write's
compare-and-swap, SG19). It is a pure read — it MUST NOT compute, write, or
move anything, and it MUST NOT lag behind *this instance's own* view after
any write this layer performs (a call to `Storage::apply`) or after a plain reopen
(`GitStorage::open`/`new` against an existing ref, which populates it from
one lookup of the ref at open time). `tip_tree` is the *only* tree id this
layer ever hands out:
there is no accessor, under any name, that takes a size argument and
returns an object id for it — this layer holds the complete tree behind
the tip, but it never renders or reconstructs one for a size other than
its current one (see "The tip-tree model", `src/lib.rs`). *Checked by:
property test — `tip_tree()` compared by direct equality against the
staging ref's own target (an independent oracle, never a second call
through this layer's own API) after every write shape this crate exposes,
including a reopen from disk; two structural syntax-tree checks (parsing
`src/`'s own `.rs` files with `syn` and walking each type's inherent impl
blocks) naming exactly two shapes: no other public method on `GitStorage`
or `GitReadOnlyView` returns an object id while also taking an argument,
and no public method on either type accepts a hasher. These checks survive
a rename of the method or its containing module (the shape they match does
not depend on either name), but they guard only those two specific narrow
shapes, not reconstruction in general -- a wrapper return type, a
trait impl instead of an inherent one, or an aliased parameter type would
each evade them; `tests/tip_tree_contract.rs`'s own header documents the
eight such evasions found and not guarded against.*

A per-algorithm root, for any size this layer has ever held — live or
historical — is not this layer's to produce: folding more than one
frontier peak's stored digest into one root needs the algorithm's own hash
fold (`bag_peaks`), a computation this layer performs nowhere in its live
write/read path (SG26 — no hash algorithm is ever named or assumed here).
A consumer that needs a root reconstructs it itself, outside this layer,
from the node digests the complete tip tree still stores.

### 4.4 `open_at(tree)` — an addition beyond the trait

**[SG21]** `open_at(tree: ObjectId) -> Result<impl ReadOnlyView, Error>` MUST
return a read-only view exposing `get_leaf`, `get_node`, and
`load_algorithm_metas` against the supplied tree object, decoded exactly as
§2–§3 specify, independent of this
instance's own staging ref and current size. It MUST NOT accept or perform
any mutation. `tree` is supplied by the caller — a `tip_tree()` this layer
recorded earlier and the caller kept, or a past checkpoint's tree the
checkpoint layer resolved through its own commit history — never a value
this layer derives internally for a size other than its current one.
Reading through a view returned by `open_at` on a tree this layer's tip
once was MUST yield the same leaf and node values `get_leaf`/`get_node`
returned when the log was actually at that tree (durable-witness parity
with `cml`'s own MMR guarantee that a proof generated before an append
remains valid after it, `docs/architecture.md`, "Conformance and
durability property tests"). *Checked by: property test.*

### 4.5 The tip-moved and transient errors

Specified as part of SG19/SG19a; repeated here because they are among the
named additions (§4.2–§4.4 and this section: `tip_tree`, `open_at`, and
these two errors). Both MUST be introspectable by the caller (each its own
distinguishable variant, an `is_tip_moved()`-style predicate optional on
top of that), and MUST never be conflated with each other, with "object
not found", or with "corrupted" — a caller's correct response differs for
each: **tip-moved** means reload and retry with fresh content (a real
concurrent write actually landed); **transient** means retry the identical
write, since nothing was ever compared or lost (`cas()` already retried
this one internally up to `RETRY_BOUND` before giving up, so a caller
seeing it at all means that bound was exhausted); neither means the stored
layout is malformed. A third, `InvalidOperation` (§4.2, SG18d), means the
batch itself was refused before anything was written because a `WriteOp`'s
own precondition did not hold; it is likewise never conflated with the
other two.

### 4.6 `metadata()` — an addition beyond the trait

**[SG30]** `GitStorage::metadata() -> LogMetadata` and
`GitReadOnlyView::metadata() -> LogMetadata` MUST each report `{ count,
kind }` for their respective tree, derived from exactly the same
`(count, has-any-`leaves/`-entry)` pair (§3.1's kind derivation) through
one shared private helper — never by decoding `meta`'s raw bytes a second
time, and never by two independently-written derivations that could drift
apart. This is the mechanism by which a caller one layer up (the
checkpoint library, §8) reads a checkpoint's kind without decoding `meta`
or reasoning about kind derivation itself. *Checked by: property test —
compared by direct equality against `NaryMerkleLog::count()`/`kind()` (the
live instance) and against the same pair recomputed independently (the
read-only view), after every write shape this crate exposes.*

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
objects — the exact "no partial state" contract `Storage::apply`
already requires — and a crash **after**
it lands leaves a fully valid `C(n')` with everything SG22–SG23 required
already reachable. There is no partial-batch state a reader can observe
through the staging ref. *Checked by: property test — kill the process at
each of several injection points around a write and assert the ref, on
restart, is either at the old or the new tree, never anything else.*

## 6. Algorithm parametricity — no hash hardcoded

**[SG26]** No function in this crate MUST name a specific hash algorithm,
reference a specific hashing library, or assume a specific digest width.
Every node this layer writes or reads is caller-supplied opaque bytes keyed
by a caller-supplied `alg_id: u64`; this layer consults no width at all
(SG15). *Checked by: source audit at implementation
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
| SG1–SG3 (key-derived layout) | Exhaustive top-level allow-list check; property tests comparing the exact set of paths under `nodes/`/`leaves/` against an independent `MemoryStorage` oracle's key set, both directions (nothing missing, nothing extra), across the full operation vocabulary and arities 2–4 |
| SG2 (`trimmed` injectivity, 256-entry bound) | Unit tests over representative keys (`0`, small, boundary, `u64::MAX`); the exhaustive set-equality property above empirically confirms the bound |
| SG6–SG7 (canonical order) | Unit test over the four top-level literals; structural walk of a real written tree confirming every sibling group is canonically sorted |
| SG8 (key-derived position lookup) | Property tests comparing this backend's reads against `MemoryStorage` over the same operation sequence, for a range of `k` and `n` |
| SG9 (purity, incl. the size-0 kind/root canonicalization) | Property tests over reordered-but-equivalent operation sequences reaching the same logical state; a genesis `C(0)` write compared across differing eventual kinds |
| SG12–SG16 (byte-exact encodings) | Golden vectors: fixed `(k, leaves, algorithms)` inputs with pinned expected object ids, one per supported object-hash format |
| SG17–SG18, SG25 (staging ref, batched write, crash safety) | Property/integration tests using two `storage-git` instances against one bare repository, one racing the other's write |
| SG18d (precondition rejection) | Direct `Storage::apply` calls asserting `InvalidOperation` for an out-of-order append, a duplicate registration, and an unregistered removal/resume, with the ref left untouched |
| SG19 (tip-moved classification) | A forced lock-contention failure (pre-created lock file) MUST NOT be reported as `TipMoved`; a genuine concurrent-writer race MUST be |
| SG19a (transient retry, bound) | A lock released within the bound lets the write succeed; a lock held past the bound forces the write to give up and return the transient variant within a generous external ceiling, never hang |
| SG20 (`tip_tree`) | Direct-equality check against this instance's own last-observed value after every write shape and after a reopen; two structural syntax-tree checks naming exactly two shapes -- no public method returns an object id together with a size argument, and none accepts a hasher -- survives a method/module rename but not a different shape carrying the same capability |
| SG21 (`open_at`) | Durability property test mirroring `docs/architecture.md`'s existing MMR durable-witness test pattern |
| SG22–SG24 (GC safety) | A test asserting the exact `write_buf_with_known_id` call path is used (SG22); a simulated missing-object recovery test (SG23); SG24 is documented, not tested |
| SG26–SG27 (algorithm and object-hash parametricity) | The full property-test suite run parametrized over at least two `Hasher` implementations of different digest widths and over both git object-hash formats |
| SG30 (`metadata()`) | Direct-equality check against `NaryMerkleLog::count()`/`kind()` on the live instance and against an independently recomputed `(count, kind)` on a read-only view |

This is the CONNECT mapping the specification workflow requires: every
normative constraint above has a named, deterministic evaluator. None is
left as prose alone.

## 8. Explicitly out of scope

Named here so absence reads as a boundary, not a gap.

- **Checkpoint commits, parents, and retention.** Wrapping a `tip_tree()`
  reading in a commit, the checkpoint ref's own forward-only
  compare-and-swap, an application's retention parents (holding a content
  or view commit alive against garbage collection), and companion ref
  edits are the checkpoint library's responsibility, one layer up. This
  layer's staging ref is not that checkpoint ref, and its
  compare-and-swap (SG17–SG19) is not a substitute for the checkpoint
  chain's.
- **Reconstructing or rendering a tree for a past size.** This layer keeps
  the complete tree behind its tip and reads a past size no other way than
  through the checkpoint layer's own commits or through `eml` reading
  directly over the nodes the current tip still contains (§2.5, §4.3).
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
