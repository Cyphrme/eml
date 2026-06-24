# Architecture

This document describes the architecture of the repository: the **PMT** kernel
and the two engineering libraries built over it, **EML** (append-only) and
**EMT** (mutable). It is the durable reference the crate documentation and the
README point back to. Every architectural claim here is checkable against the
source; the relevant paths are cited inline.

## The three layers

The code is cut into three layers, with volatility decreasing downward — the
abstract core changes least, the application instantiations most.

```
┌──────────────────────────────────────────────────────────────────────┐
│ Layer 1 — PMT  (Polymorphic Merkle Tree kernel)        crate: pmt      │
│   proof spine · canonicalization (collapse + promotion) · Hasher seam  │
│   inclusion · leaf proof · binding proof · binding root · coupling     │
│   Sealed currency · opaque metadata channel                            │
│   depends on nothing                                                   │
└───────────────────────────────┬────────────────────────────────────────┘
                                 │  abstract core → engineering mechanism
              ┌──────────────────┴───────────────────┐
┌─────────────▼──────────────────┐      ┌─────────────▼──────────────────┐
│ Layer 2 — EML                   │      │ Layer 2 — EMT                   │
│  append-only log    crate: eml  │      │  mutable tree       crate: emt  │
│  frontier-stack carry           │      │  rebuild / path-recompute       │
│  consistency proofs             │      │  set / get; no consistency      │
│  snapshot proof · filling       │      │  retroactive per-node alg add   │
└─────────────┬──────────────────┘      └─────────────┬──────────────────┘
              │                                        │
   ┌──────────┴───────────┐                  ┌─────────┴──────────┐
   │ cyphr-log (k=2)       │                  │ cyphr-tree (k=2)   │
   │ CT / RFC-9162 build   │                  │ …                  │
   └───────────────────────┘                  └────────────────────┘
     Layer 3 — application instantiations (consumers; may leave the repo)
```

Both engineering libraries depend only on the kernel, never on each other; the
one currency they exchange is the kernel's `Sealed` (`pmt/src/sealed.rs`). No
kernel or engineering crate carries an application concept.

## Layer 1 — PMT, the kernel

PMT (`pmt/src/lib.rs`) is the abstract core every tree shares. Its motivation is
**polymorphic hashing** — a single structure addressable under many hash
algorithms at once (multihash agility) — and its contents are the non-arbitrary
choices that make that work.

### The Hasher seam

A construction reaches its hash through one trait, `Hasher`
(`pmt/src/hasher.rs`). Five methods are required: `leaf`, `node`, `empty`,
`hash`, and `clone_box`. Two have defaults: `null` (derived from `hash`) and
`digest_len` (derived from `empty`). The **fixed-width contract** — every digest
a single hasher produces must be the same constant byte length — is
load-bearing: the unprefixed node-hash concatenation is injective in its child
boundaries only when all children are the same width, and binding-root soundness
rests on that injectivity. Prefix domain separation is deliberately **not** a
kernel axis — `leaf(d)` is `H(d)` with no prefix byte, and an application that
wants domain separation supplies a prefixing `Hasher` wrapper. This keeps the
libraries parameterized essentially by the arity `k` alone.

One identity follows directly: because `leaf(d) = H(d)`, a leaf whose payload is
the four bytes `null` hashes to the same digest as the null constant
`null() = H(b"null")`. The kernel treats this as intentional and inert: activity
is read from the committed epoch timeline (below), never inferred from a digest
equaling the null constant, so a correct verifier is never fooled by it. An
internal node digest cannot equal `null()` except by a true hash collision —
a node preimage concatenates two or more digests and so is far longer than the
4-byte `b"null"` preimage (`pmt/src/hasher.rs`, the `null` doc comment).

### The proof spine

The proof spine (`pmt/src/topology.rs`) is the kernel's topological strategy:
a **constant k-ary spine** whose shape is fixed entirely by `(tree_size, arity)`,
with **n-ary subtrees** hanging below it to recover full Merkle generality. For
a given size, a log decomposes into a *frontier* of perfect k-ary subtrees
(`frontier_for_size`), which fold into one root by repeatedly grouping the
rightmost `k` (`fold_frontier`). The shape of an inclusion proof — its length
and, per step, the path node's position and sibling count — is fully determined
by `(tree_size, arity, index)` and is computed by a single function,
`inclusion_skeleton`.

That single function is the load-bearing detail: the verifier reconstructs the
canonical topology and checks a proof's steps field-by-field against it
(`verify_inclusion_path_structure` in `pmt/src/proof.rs`), and proof generation
emits the same skeleton (`within_subtree_path` in `pmt/src/mr.rs`). Keeping one
derivation source is what prevents producer and verifier from drifting into
disagreeing topologies. Because there is no per-node domain separation,
second-preimage safety rests entirely on this exactness. The frontier
decomposition is the same construction certificate-transparency logs and
Merkle-mountain-range accumulators use (their "peaks"); the spine generalizes it
to any arity `k` in `2..=256` (`ARITY_RANGE`).

Its payoff is bounding the most expensive part of proof traversal: the spine is
the worst case, and it is constant for a given size.

### Canonicalization: collapse and promotion

Canonicalization (`pmt/src/mr.rs`) is one generic reduction over an arbitrary
Merkle structure, applied structurally on every fold — always on, never a
per-construction toggle. It composes exactly two primitives:

- **promotion** — a lone (single) child is lifted in place of the wrapping
  hashed node. It is *structurally deterministic*: a verifier re-derives it on
  reconstruction. In `nary_mr`, a one-child fold returns that child; in proof
  encoding, a promoted node contributes no step (`within_subtree_path` emits a
  step only for multi-child nodes). This is the same path compression a
  PATRICIA / radix trie performs.
- **collapse** — children of the *same value* fold to that value
  (`pmt/src/mr.rs:61-67`): any equal-sibling run collapses to that shared value,
  not only null runs. This is the node-elimination rule of a reduced ordered
  binary decision diagram (ROBDD rule R2: eliminate a node whose children are
  isomorphic). The all-null/inactive run is the dominant instance — it is the
  only per-algorithm-divergent collapse, because equal-value non-null runs are
  the same under every algorithm and their geometry needs no separate commitment
  — but the fold is general same-value.

Treating these two as a single confluent reduction to a unique canonical form is
the kernel's structural contribution. ROBDD canonicalization is the rigorous
template — its reduce procedure proves a unique canonical normal form, and its
R2 is `collapse` — but no published work casts generic *Merkle* canonicalization
as one reduction composing these two primitives; that framing is original to
this work. Orthogonal axes are kept separate and below the authentication
boundary: subtree deduplication / hash-consing is a *storage* concern (ROBDD
rule R1, tree → DAG) and entropy coding is a *serialization* concern, neither of
which changes a root.

A strict-binary construction (the CT / RFC-9162 build) obtains its shape by
*banning n-ary subtrees and fixing `k = 2`* — not by disabling canonicalization,
which always runs.

#### What canonicalization commits

The two primitives are asymmetric in what they must commit:

- **Promotion commits nothing.** Because a verifier re-derives a lone-child lift
  deterministically, no metadata is needed to recover it. A promoted singleton
  leaf (a height-0 frontier node) emits no run-extent (`pmt/src/sealed.rs`,
  `RunExtent` doc).
- **Collapse commits its minimal run-extent.** A contiguous equal-value run is
  lossy without the count, so the kernel commits the run length — how many
  leaves a collapsed subtree stands for. These extents are the
  `height >= 1` nodes of the frontier, derived from `(tree_size, arity)` alone
  (`Sealed::run_extents` in `pmt/src/sealed.rs`), never inferred from a digest.

The committed extent is load-bearing for soundness, not merely for
decompression: two distinct log entries that happen to be equal are distinct
events, and the committed multiplicity preserves their distinct positions when a
tree is unrolled. Null-run extents carry the activation geometry (below); the
extent geometry recovers the rest.

### Epoch construction and the committed activation

Multihash agility needs a data model for *which* algorithms are live over *which*
positions, because activity cannot be inferred from a digest. The kernel tracks
this as a **committed epoch timeline** per algorithm: a vector of disjoint,
ordered `(start, end)` intervals, with an open final interval (`end == u64::MAX`)
for a live algorithm (`pmt/src/proof.rs`). The timeline is the internal source
for "is algorithm X active at position p?" (`committed_active_at`) and "what is
the active set?" (`committed_active_algs`). `validate_committed_epochs` enforces
strict sort by algorithm ID, ordered non-overlapping intervals, and a single
trailing open interval.

A timeline is **trivially covered** when every algorithm is active from genesis
(`[(0, u64::MAX)]`). Triviality is informativeness, not registry cardinality: many
open-from-genesis algorithms are still trivial, while a single algorithm with a
pre-activation prefix, a deactivation, or a gap is non-trivial.

What gets *committed* into each binding root is not the raw epoch timeline but
its geometric consequence: the **null-run-extents** — the maximal aligned k-ary
blocks over which each algorithm has no active content. These are the only
per-algorithm-divergent collapse instances (null is the only value whose run
geometry differs between algorithms), and they are the minimal information needed
to reconstruct a verifier's view of the activation. `null_runs_for_alg` derives
them from the epoch timeline; `all_null_runs` collects them across all algorithms;
`serialize_null_runs` is the fixed-width, injective serialization committed in
every binding root.

### The binding root

The **binding root** is the live primary root of both trees: the head every
per-algorithm root authenticates against. It is *not* a bespoke hash — it is the
same canonicalization fold (`nary_mr`) applied one level up, over the
per-algorithm **member roots as children** (computed by `combined_root` in
`pmt/src/proof.rs`):

```
combined_root(H, member_roots, alg_epochs, tree_size, arity)
  = nary_mr(H,  [MR₀, MR₁, …]  ‖  [H(serialize_null_runs(...))]?)
```

A **member root** is one algorithm's own raw root (the fold of its frontier
peaks under its own hash; `Sealed::member_root`). The member roots enter the
fold as **opaque digests** — `H` is only ever applied to those digests and to
the null-run serialization, never to another algorithm's security material — so
each algorithm's binding root rests solely on its own hash. This is why no
algorithm's break can weaken another's, even inside the shared head.

Two facts make this a fold rather than a special-cased commitment:

- **Singleton promotion is native.** A registry of one algorithm folds
  `nary_mr(H, [MR₀])`, whose one-child arm promotes to `MR₀`. The binding root
  *is* the member root because there is one child — there is no promotion
  predicate, and so no branch to forget. This is what makes a single-algorithm
  tree's root identical to a plain (e.g. RFC-9162) root with no binding-root
  overhead.
- **Coverage is a sibling, present only when informative.** A multi-algorithm
  structure with any non-trivial activation must commit the null-run-extents —
  the per-algorithm-divergent collapse geometry — so a verifier can reconstruct
  the canonical structure. It enters the fold as one extra **coverage child**
  `H(serialize_null_runs(alg_epochs, tree_size, arity))`, appended **iff** the
  null runs are non-trivial (`null_runs_are_trivial`). A trivially covered
  structure carries no per-algorithm-divergent collapse, so its child is omitted;
  the absence of the child *is* the trivial encoding. The null-run serialization
  is fixed-width and therefore injective over its boundaries (`serialize_null_runs`).

So a single algorithm with no null runs yields a binding root equal to its member
root; any non-trivial activation yields a genuine `nary_mr` node. EMT has trivial
coverage (its cells are all-covered); EML carries the epoch timeline whose null
runs record crypto-agility boundaries.

#### What the binding root commits

It commits the per-algorithm member roots — which intrinsically carry the
collapse/promotion geometry, by canonical uniqueness — and, when non-trivial,
the null-run-extents of all algorithms through the coverage child. It does
**not** mix security across algorithms.

### Coupling — opening the binding root

A `CouplingProof` (`pmt/src/proof.rs`) is the single primitive that opens a
binding root to its children: the per-algorithm raw roots together with the
committed epoch timeline (and, through it, the null-run-extents). Its
`authenticate` method revalidates structure (canonical ordering, DoS bounds,
well-formed epochs, an active set consistent with the timeline) and recomputes
the binding root via the same `combined_root` fold; on success both the roots
and the timeline are authenticated by the head. The inclusion- and
inactivity-with-coupling helpers (`verify_inclusion_with_coupling`,
`verify_inactivity_with_coupling`) compose this opening with an inclusion check,
enforcing the one-directional `inactive ⇒ null constant` rule: at a position
the timeline marks inactive for an algorithm, the leaf must be the null constant;
active positions are unconstrained.

### The binding proof — cross-algorithm consistency

Where coupling opens *one* binding root, the **binding proof**
(`pmt/src/binding_proof.rs`) is the first-class, cross-algorithm peer of the
inclusion / consistency / leaf / snapshot proofs. It proves that a set of
per-algorithm binding roots (each the binding root computed under its own hash)
are mutually consistent — that every algorithm committed to the *same* member-root
tuple and the *same* activation geometry.

A `BindingProof` carries only the shared structure (member roots + epoch
timeline); the binding roots `BR_i` are supplied to `verify` as **trusted
inputs**, paired with each algorithm's own hash (`TrustedBindingRoot`). For each
trusted root the verifier recomputes `combined_root(H_i, member_roots,
alg_epochs, tree_size, arity) == BR_i`. If
every algorithm matches, the algorithms are mutually bound (`BR_i ≘ BR_j`).
Verification reads **digests only** — no leaf payloads, no proof paths.

The proof establishes consistency *given* trusted binding roots; it never
establishes their origin. A consumer roots that trust out of band, via an
optional attestation on the opaque metadata channel. This is the honest trust
contract: supplying an unauthenticated `BR_i` makes the guarantee vacuous,
exactly as a forged `root` does for `verify_inclusion`. Soundness everywhere in
this layer is therefore **relative to the verifier's trusted algorithm list**:
the verifier supplies the accepted algorithm IDs and their ordering (the
`expected_active_algs` argument), which fixes the digest widths and makes the
member-root fold unambiguous.

### The leaf proof

A `LeafProof` (`pmt/src/leaf_proof.rs`) is the peer of the inclusion proof over
the *same* shared positional topology, packaged as a self-contained witness: a
leaf hash bound to its trusted positional parameters `(index, tree_size,
arity)` plus the path, so a consumer asks one question — `verify(hasher,
root)`. It runs over a **live** tree and is exposed by *both* EML and EMT; it is
not consistency-coupled, and it is the base case the snapshot proof composes.

### Inclusion and its trust contract

`verify_inclusion` (`pmt/src/proof.rs`) binds a leaf hash to a log position by
reconstructing the exact topology from `(index, tree_size, arity)` and
rejecting any deviation; the proof supplies only sibling digests. Those
parameters and the `root` are **trusted** — they must come from an authenticated
source (a signed tree head or trusted checkpoint), never from the proof or
caller-untrusted input. A `true` result binds the leaf to its position only;
payload activity is a separate, timeline-authenticated question.

#### Canonical proof encoding and non-malleability

Every accepted step must carry at least one sibling. A zero-sibling step would
represent a promoted (lone-child) node — an inert no-op whose parent equals its
child without hashing — so honest provers omit such steps and the verifier
rejects them (`reconstruct_inclusion_root`). Omitting a promoted step never
changes the computed root, so completeness is preserved; in exchange, a fixed
`(leaf_hash, index, tree_size, root)` admits at most one accepting path (modulo
hash collisions), which closes prepend/insert malleability. This concerns
zero-*sibling* steps only; null-*valued* siblings from a collapse are unaffected.

### Subtree opacity

Any tree's root can be carried as an **opaque leaf** in any other tree: a caller
places the root bytes directly into `Subtree::Leaf(root_bytes)`
(`pmt/src/subtree.rs`), which is byte-identical to any other raw-payload leaf
carrying the same bytes. The kernel never branches on a leaf's origin — there is
no `is_embedded` tag. Composition is two independent inclusion verifications,
with no composite proof type. The opacity is a security property: an auditor
cannot tell whether a leaf is a raw payload or a child-tree root, so embedded
subtrees cannot be fingerprinted.

### The opaque metadata channel

`Meta` (`pmt/src/metadata.rs`) is an arbitrary, opaque byte buffer attached to a
commitment. The kernel never reads, validates, signs, or branches on its
contents — round-trip fidelity is the only guarantee. The type names no signing
scheme; the fact that an out-of-band tree-head attestation *may* ride here is
purely a consumer convention, invisible to the kernel. This is where the trust a
binding or snapshot proof requires is established, keeping the kernel
signature-agnostic.

## Layer 2 — EML and EMT, the engineering libraries

The two engineering libraries move from the abstract core to a concrete
mechanism. Each shares enough — generalizable proof semantics, the kernel
surface — to be its own hard-named library, and the append-only-vs-mutable split
is what decides which proofs are sound.

|                       | **EML — append-only log** (`eml`) | **EMT — mutable tree** (`emt`) |
| :-------------------- | :-------------------------------- | :----------------------------- |
| Regime                | append-only                       | mutable (`set` / `get`)        |
| Representation        | frontier stack (bounded carry)    | rebuild / path-recompute       |
| Consistency proofs    | **yes**                           | **no** (unsound under mutation)|
| Inherits from PMT     | spine, canonicalization, epochs, binding root, coupling, binding proof, inclusion, leaf proof, metadata | same, minus consistency |
| Adds                  | snapshot proof, filling           | retroactive per-node alg add   |
| Config                | `k`                               | `k`                            |

Pinning the proof semantics at this layer means "is a consistency proof valid?"
is answered by the *library* — EML yes, EMT no — uniformly across every
application instantiation.

### EML — the append-only log

EML (`eml/src/lib.rs`) owns the append-only mechanism: the frontier carry, the
log builder, storage, and the consistency surface (`ConsistencyProof`,
`verify_epoch_evolution` in `eml/src/proof.rs`). It re-exports the whole kernel
surface so consumers reach the library through one crate. Its representation is
the frontier stack — the bounded continuation state — which is itself an
optimization of the proof spine.

### EMT — the mutable tree

EMT (`emt/src/lib.rs`) is the mutable peer, built fresh here. It lets interior
cells change (`set` / `get`), so it keeps **no frontier and no consistency
proofs**: the frontier's left-subtrees-are-sealed assumption is unsound under
mutation. It is positional and dense, shares the kernel's proof-spine index
space, and supports inclusion proofs, non-membership (inclusion of the kernel
null constant via collapse), the leaf proof, and **retroactive per-node
algorithm addition** at `O(log n)` (`Emt::add_algorithm_at`) — a single node
gains a digest under a new algorithm and the root is recomputed by
path-recompute. Verification stays in the kernel: an EMT proof is checked with
`pmt::verify_inclusion` against an authenticated `(index, tree_size, arity,
root)` (`emt/src/tree.rs`). Its materialized root equals a from-scratch kernel
evaluation of the canonical subtree — an oracle test pins the spine to PMT
semantics (`emt/src/lib.rs`, `root_matches_kernel_evaluate`).

Retroactive per-node addition (an EMT mutation, `O(log n)`) is distinct from
**filling** (an EML operator, `O(n)`): the former gives one node a new digest;
the latter rebuilds a whole algorithm's gapless history over the real data.

## The seal lattice

There is exactly one commitment currency, the kernel's `Sealed`
(`pmt/src/sealed.rs`). Both a mutable EMT and an append-only EML seal into it,
and every consumer reaches the same operations from it.

### Sealed — one commitment, several derived views

A `Sealed` stores the **resumable frontier**: per algorithm active at the sealed
size, the digests of the perfect k-ary subtrees the frontier names (the
"peaks"), plus the committed timeline and the optional metadata channel. Its
fields are private; the only ingress is `Sealed::new` (which validates the
timeline and cross-checks the peak count against the canonical frontier
geometry) and the only egress is a read borrow or a derived view. There is no
`unseal` and no field mutator, so a value cannot be walked back to the
construction it came from — the seal is **one-way**.

Everything else is a **derived view**, computed on demand and never stored,
because this metadata is provably derivable from the tree rather than tracked as
a parallel committed channel:

- the **member root** is the fold of an algorithm's frontier peaks
  (`Sealed::member_root`);
- the **binding root** is the `combined_root` fold over the member roots and
  timeline (`Sealed::binding_root`), with native singleton promotion;
- the **run-extents** are the `height >= 1` frontier nodes, pure
  `(tree_size, arity)` geometry (`Sealed::run_extents`).

### The four ways forward from a seal

The seal is one-way, but a `Sealed` is the basis for an orthogonal operation
set, each keyed by what it needs:

- **verify** — the proofs check against the `Sealed`'s derived roots; needs
  nothing but the `Sealed`.
- **resume** (`NaryMerkleLog::resume`, `eml/src/tree.rs`) — reopens an
  append-only log onto the committed frontier and appends forward. It is
  **data-free**: only the peaks are carried, so a resumed log cannot read the
  committed past — exactly the one-way guarantee. Folding the seeded frontier
  reproduces each algorithm's sealed member root, so a consistency proof bridges
  the resume.
- **fill** (`fill`, `eml/src/filling.rs`) — the **trustless** path. It consumes
  the `Sealed` *and* the real historical leaf data, rebuilds a full readable
  single-algorithm tree (as an EML or EMT, the caller's choice), and **verifies
  the rebuilt binding root against the committed one**. A target the data cannot
  reproduce — wrong leaves, a layout the chosen kind cannot rebuild — yields a
  mismatch and is rejected. Both inputs are mandatory and neither substitutes
  for the other: because a log abstracts its leaves by hash, only the
  data-holding operator can fill. Its purpose is to *raise the certainty of the
  past* (harden a history under a possibly-weakening algorithm), not to migrate.
- **no `EMT::from_sealed`** — there is deliberately no way to revive a mutable
  tree from a seal (`emt/src/tree.rs`). A frontier is the *complete* continuation
  state of an append-only log but only *partial* state for a mutable tree:
  mutating an interior cell needs every cell's digest along its ancestor path,
  and the seal kept only the peaks. Reviving mutation would also un-seal the
  committed past. The way to a readable tree over committed data is `fill`,
  which discards the unused frontier.

### The snapshot proof

The **snapshot proof** (`eml/src/snapshot_proof.rs`, owned by EML) is the
aggregate peer of the other proofs, answering "are these leaves legitimately in
the sealed commitment?" in one self-contained witness. Its base case is the PMT
leaf proof: a sequence of leaf proofs verifies against the sealed member roots,
and the member roots bind to the **trusted** binding roots (the same
`TrustedBindingRoot` contract as the binding proof). One head recomputation per
algorithm binds all the member roots at once, never a literal per-leaf
recursion; the wire format is deliberately abstract, the duality being design
intuition rather than a binding encoding. As with the binding proof, the binding
roots are trusted inputs whose origin a consumer establishes out of band via the
opaque metadata channel.

## Layer 3 — application instantiations

Concrete, opinionated, domain-specific; names matter least here. A `cyphr-log`
(EML at `k = 2`) is the working append-only target; a `cyphr-tree` (EMT at
`k = 2`) is its mutable peer. A CT / RFC-9162 build (EML at `k = 2`, n-ary
subtrees banned, hash-prefixed) is a research artifact: RFC-9162's leaf/node
prefix distinguishes inner from leaf hashes, which contradicts general promotion
(a promoted lone child must be indistinguishable from a plain node), so the
prefixed build is a build-time artifact rather than the unprefixed working
target.

The CT subtree-ban is a **runtime `LogKind` lock** on a generic EML log, not a
type-level prohibition. `LogKind` is fixed on the first append: a log that
receives its first append as a flat leaf (`append_leaf`) locks to `LogKind::Flat`
and rejects any subsequent `append_subtree`, and vice versa. The CT build
(`ct/src/lib.rs`) creates logs via `append_leaf` only; the contract is enforced
at runtime, and `append_subtree` remains callable on an empty CT log before the
first append.

The repository's contribution is **PMT + EML + EMT**; the instantiations are
consumers and may move out of the repository later.

## Formal guarantees

The core is formally verified in Lean 4 (`proofs/lean/`; see
`proofs/lean/README.md` for the reviewer's guide). Two properties bound what
the verification rests on:

- **Sorry-free.** Every theorem in the corpus is complete — no `sorry`
  placeholder appears in any proof.
- **A small trust base — at most four structural axioms.** The entire trusted
  computing base is declared in `proofs/lean/EMLProof/Foundations.lean`: an
  abstract digest type `Digest`, its non-emptiness `Digest.nonempty`, the
  abstract hash `H`, and the serializer `digestToBytes`, together with Lean's own
  built-ins (`propext`, `Classical.choice`, `Quot.sound`). Collision resistance
  is **not** an axiom — it is discharged as an explicit hypothesis at each use
  site, so the trust base never assumes `H` injective. `#print axioms` on every
  downstream theorem reports a subset of these four plus the built-ins, and never
  `sorryAx`.

The named theorems, by layer:

- **Canonicalization** — `canonical_unique`
  (`proofs/lean/EMLProof/Canonical.lean`): a structure reduces to a unique
  canonical normal form, the injectivity that pins a layout to its root.
- **Inclusion** — `kary_inclusion_soundness` (`Kary.lean`) and
  `inclusion_soundness` (`NEML.lean`): an accepting canonical proof commits the
  leaf at the claimed log position; `inclusion_proof_unique` (`NEML.lean`):
  non-malleability — at most one accepting canonical path per statement, modulo
  an internal-node hash collision.
- **Binding root and coupling** — `combinedRoot_binds_timeline`,
  `coupling_extract_sound` (`NEML.lean`): the binding root is the `nary_mr` fold
  over the member-root child digests plus the coverage child, so a fixed root
  pins the member-digest list (modulo a node-hash collision) and binds the
  timeline; algorithm identities are the verifier's trusted active-set input, not
  recovered from the root.
- **Binding proof** — `binding_root_sound`, `binding_proof_consistent`
  (`BindingProof.lean`): each algorithm's binding root folds under its own hash,
  and mutually consistent trusted binding roots prove agreement on the shared
  structure.
- **Leaf and snapshot proofs** — `leaf_proof_sound` (`LeafProof.lean`) and
  `snapshot_proof_sound` (`SnapshotProof.lean`, composed from the leaf proof),
  each built over the four-axiom `Foundations`.
- **Consistency (EML)** — `consistency_soundness` and `consistency_append_only`
  (`KaryConsistency.lean`): an accepting consistency proof against the honest
  current root forces the reconstructed old root to the genuine size-`oldSize`
  prefix root, and lifts to the data-level append-only relation
  `oldCells <+: newCells`. EMT has no consistency theorem because it has no
  consistency proof.
