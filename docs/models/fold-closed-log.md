# MODEL: Fold-Closed Claim Log

<!--
  Formal domain model for querying an append-only Merkle log of claims
  without a separately maintained index. Characterises exactly which
  queries the log's own structure can serve (the list-homomorphism class),
  places range summaries in the log as claims subject to the same trust
  algebra as every other claim, and derives the design obligations this
  imposes on the claim algebra.
-->

**Audience.** Engineers and formal-methods readers designing the claim
algebra that the log will carry. Part I is the working explanation; Part II
is the model it rests on. Familiarity with the Merkle spine
([architecture](../architecture.md)) is assumed; category theory is not.

**Answer.** An append-only Merkle log needs no stored structure — its shape
is arithmetic on its size `n` — and its interior hashes carry no information
about content. Consequently the log can serve, with no separately tracked
index, **exactly the queries that are list homomorphisms over its leaves**: a
monoid-valued measure of each claim, an associative fold over ranges, and a
finalizer. Range summaries are themselves **claims appended to the log**,
reproducible by replay and corroborated under the same algebra as everything
else. The interior carries only a small, fixed pruning signal. What the claim
algebra must therefore deliver is (1) a summary monoid per query kind and
(2) **locality** — obligations that are discharged near where they arise —
because associativity makes the fold *correct* and locality makes it *cheap*.
Where locality cannot hold — succession, e.g. key rotation — a structural
**lease** restores the bound and makes expiry provable.

---

## Part I — Plain reading

### The shape costs nothing

For an append-only log the tree's shape is a pure function of the leaf
count. Every structural question — where leaf `i` sits, which nodes are the
current peaks, what the inclusion path for leaf `i` at size `n` is — is bit
arithmetic on `(i, n)` ([spine topology](../../spine/README.md)). A snapshot
is one integer plus a root and a seal. Every historical version is a prefix
of one flat array. There is nothing to reconstruct, so "cheaply reconstruct
the shape in memory" is already solved: the shape is never stored.

### The shape knows nothing about content

A Merkle tree is an index over exactly one axis: sequence position for a log,
key for a keyed tree. Interior hashes are opaque. A query on any other
attribute is a full scan of leaf payloads, and materialising the tree more
cheaply does not change that — there is nothing in the structure to prune
with.

So "avoid maintaining an index" cannot mean "the shape answers the query".
It can only mean the index is **derived** rather than **tracked**: a pure
function of the log prefix, reconstructible from it, ideally committed by it,
never independent mutable state that can drift or must be trusted.

### What a fold buys

Suppose every claim maps to a value in some type `M` with an associative
combine `⊕` and an identity `ε` — a **monoid**. Then the summary of any range
of claims is the fold of their values, and because `⊕` is associative the
fold can be grouped any way at all — in particular along the tree's own
subtrees. Any range `[a, b)` decomposes into at most `2·log₂ n` perfect
subtrees, so if summaries exist at subtree granularity a range query touches
`O(log n)` summaries instead of `b − a` leaves. Selection by predicate works
the same way: a summary that shows a subtree cannot contain a match prunes it
whole.

This is a segment tree, and it is the *only* kind of acceleration a tree can
offer. The precise statement is: **the structure serves a query iff the query
is a list homomorphism** — a monoid-valued measure followed by a finalizer.
Bird's third homomorphism theorem gives the practical test: if you can
compute the answer by a single forward scan *and* by a single backward scan,
an associative combine exists and the structure serves it. If you cannot, no
Merkle shape will help, and that query needs a genuinely external index.

### Summaries are claims

Where do the summaries live? Two places, with different roles.

- **Rich, evolving summaries live in leaves.** A summary of range `[a, b)`
  under measure `M` is a claim like any other: authored, signed, attributable.
  Its obligations are "range `[a, b)` at root `R`", and anyone can discharge
  them by replaying the range. A summary claim is therefore *reproducible* in
  exactly the sense a reproducible build is, and the trust algebra applies to
  it unchanged. Introducing a new summary kind is introducing a new claim kind:
  the tree, its preimages, and the proof corpus do not move.
- **A small, fixed pruning signal lives in the interior.** A count plus a set
  sketch of the hashes referenced within the subtree, computed along the
  `O(log n)` carry path on every append and bagged over the peaks exactly as
  the hashes are. This is structurally forced, available at every subtree
  without anyone appending anything, and — if placed in the hash preimage —
  authenticated by the root. It is deliberately minimal because it is fixed at
  design time.

Summary leaves need a discovery rule or they are as good as lost. The clean
rule is to look them up by key `(kind, range)` in a keyed tree derived
deterministically from the log; any range decomposes into `O(log n)` dyadic
keys. The alternative — appending a summary leaf on a schedule tied to the
carries — works but interleaves metadata with data leaves.

### Corroboration is a fold

The motivating case: a claim is *corroborated* when a subset of other claims
discharges everything it depends on — a reproducible build together with its
entire provenance. Let a summary be a pair `(facts, obligations)` of reference
sets, combined by

```
(F₁, O₁) ⊕ (F₂, O₂) = (F₁ ∪ F₂, (O₁ ∪ O₂) − (F₁ ∪ F₂))
```

This is associative and commutative with identity `(∅, ∅)`; "claim `c` is
corroborated at size `n`" is "`c`'s obligations are empty in the fold over
`[0, n)`". A **causal** variant, in which only *earlier* facts may discharge
an obligation, is also a monoid (non-commutative; Part II §5). Either way,
corroboration is in the served class.

### Where it stops: size and locality

Associativity is rarely the problem. **Summary size** is. The corroboration
monoid is total but unbounded — obligation sets can grow with the log — and a
subtree summary only prunes if it is small enough to read cheaply. Two things
bound it:

- **Sketches.** A Bloom filter or similar over referenced hashes gives an
  approximate prune with a tunable false-positive rate; exact resolution goes
  through the keyed tree.
- **Locality.** If obligations are usually discharged within a bounded
  distance of where they arise, subtree summaries stay small in the common
  case. Provenance is highly local in practice — a build's inputs were logged
  before it and are referenced by hash. Where locality fails the fold is still
  correct; it just stops being cheap. Locality also says nothing about
  dependencies that *never* arrive: a permanently dangling reference stays in
  every summary that contains it, so the algebra must bound those too.

Locality is a property of the claim algebra and of how claims are emitted,
not of the tree. It is the design lever — but it constrains less than it
first appears. With position-qualified references (below), checking one
claim under *causal* corroboration is just resolving its `|deps|`
references, no fold at all. Locality and dangling obligations only bound
the aggregate questions and the symmetric case, where a dependency may be
discharged by a claim that arrives later. Worst cases for every component
are tabulated in Part II §10.

### Succession under lease: bounding the forward query

Locality has one systematic failure: **succession**. A key rotation refers
back to the claim it replaces, and it can arrive at any time, so no window
around the original bounds it. Backward references are free in a hash
structure; forward references — from the original to its latest successor —
are impossible without invalidating the tree. "What is the current key for
`X`" is a forward query, and without help it means scanning to the tail or
keeping a keyed index by origin.

A **lease** converts it into a bounded backward range query. Give every key
state a structural expiry: it is valid at size `n` only if renewed within the
last `L` leaves. Then if `X`'s chain is alive at `n`, its latest renewal lies
in `[n − L, n)`, and the current successor is the highest-positioned claim
with `origin = X` in that window. The contrapositive is the real gain: no
such claim in the window means `X` is **expired**, decided — and, if the
window summaries are committed, *proven* — in the same bounded work. Absence
is what forward references can never give you; the lease gives it back.
Historical queries come free: "successor as of `n₀`" is the same query over
`[n₀ − L, n₀)`.

Succession is a fold. Summaries map each origin to its latest `(pos, ref)`
in the range, combined by taking the higher position. A span-`s` block holds
at most `s` origins, and the window decomposes into `O(log L)` blocks of span
`≤ L`, so every summary the query reads is bounded by `L`. Walking back from
the tail becomes `O(log L)` summary reads.

*Verifying* the found successor is not a scan: it is a walk of the chain's
own `predecessor` links back to `X`, one signature check per hop. Make
references **position-qualified** — `(pos, digest)` rather than a bare
digest — and each hop is one array read plus a hash comparison, with no
hash-to-position lookup anywhere; a wrong `pos` fails the hash check, so the
position is self-verifying. The one honest residual is the walk's *length*:
the lease forces a renewal at least every `L` leaves, so a key alive for `A`
leaves has `≥ A / L` links, and a cold verification is linear in the key's
age. No structure checks `m` independent signatures in fewer than `m`
checks. A checkpoint amortises it: a summary claim "chain of `X` valid
through `c_j` at root `R`" is reproducible under the same trust algebra, so
verifying the current key is one link plus one checkpoint, and the full walk
is paid once per chain rather than once per query.

Four things the algebra must supply:

- every rotation carries both an `origin` and a `predecessor` reference,
  each position-qualified as `(pos, digest)`;
- a global `L_max` — one unbounded lease unbounds the window for everyone;
- leases in leaf index, not wall-clock (a max-timestamp signal can translate
  time to position in `O(log n)` if the algebra needs it);
- a fork policy for two successors of one predecessor, detectable by a count
  per `(origin, predecessor)`.

### What the claim algebra must deliver

For each query kind the algebra must supply:

1. A summary type `M` with an associative `⊕` and identity `ε`.
2. A measure `μ` from each claim kind into `M` (kinds that do not participate
   map to `ε`).
3. A finalizer from `M` to the answer.
4. A bound on `|M|`, or a sketch that bounds it with a stated error.
5. A locality expectation, so the cost model is honest.
6. A placement: leaf summary (evolvable) or interior signal (fixed).

Different query kinds tuple: a product of monoids is a monoid, and adding a
kind later adds a component in which old summaries carry `ε`. Point lookup by
identity is not in this class for a sequential log and routes through the
derived keyed tree. Joins across arbitrary attributes are outside the class
altogether.

---

## Part II — Formal model

### Domain Classification

**Problem Statement.**

Given an append-only Merkle log whose leaves are structured claims, and a
query language over those claims, characterise the queries the log can
answer in `O(log n)` structural work without a separately maintained index;
place the auxiliary data those queries need inside the log's own trust
model; and derive the constraints this imposes on the claim algebra.

**Domain Characteristics.**

- **Structure.** Shape is a function of size (Merkle Mountain Range).
  Positions, peaks, and paths are arithmetic on `(i, n)`.
- **Content.** Leaves are claims with a priori structure; interior nodes are
  digests, opaque to content.
- **Queries.** Pure functions of a leaf range. Acceleration is possible only
  through associative decomposition over subtrees.
- **Trust.** Auxiliary data (summaries) must be attributable and reproducible
  under the same algebra as the claims themselves.

### Formalism Selection

| Aspect                  | Detail                                                     |
| :---------------------- | :--------------------------------------------------------- |
| **Primary Formalism**   | Monoids and list homomorphisms (Bird–Meertens)             |
| **Supporting Tools**    | Dyadic interval decomposition; product monoids; sketches   |
| **Rationale**           | Associativity is exactly the property subtree folds need   |

**Alternatives considered.**

- **Annotating every interior node with rich summaries** (finger-tree
  measures baked into the structure). Rejected as the primary mechanism:
  fixes the summary type at design time and moves the hash preimage. Retained
  only for the minimal pruning signal (§7).
- **A separate tracked index.** Rejected: independent mutable state outside
  the trust model; the thing this model exists to avoid.
- **A keyed Merkle tree as the authority.** Rejected: loses prefix-stable
  durable witnesses. Retained as a *derived* structure (§6).

### §1. Carrier Types

```
Claim   — A structured leaf payload. Has a kind and a set of references.
Ref     — A content reference (digest) to a claim or artifact.
ℕ       — Leaf indices, sizes, heights.
Range   — Half-open intervals [a, b) ⊆ [0, n).
M       — A summary monoid (M, ⊕, ε): ⊕ associative, ε two-sided identity.
Log     — A finite sequence of claims c₀, c₁, …, c_{n−1}.
```

### §2. Shape as a Function of Size

The log is stored as a flat post-order array of digests. For the binary
case (`k = 2`, zero-indexed leaves):

```
nodes(n)    = 2n − popcount(n)                  — array length at n leaves
pos(i)      = 2i − popcount(i)                  — position of leaf i
peaks(n)    = one peak per set bit h of n,       — a perfect subtree of 2^h
              of height h, laid high bit first     leaves ending at that bit
```

Parent, sibling, and height of a position are `O(log n)` bit operations. The
inclusion path of leaf `i` at size `n` is a function of `(i, n)` alone. For
general `k` the same statements hold over base-`k` digits
([`spine::frontier_for_size`](../../spine/README.md);
[`cml::mountain`](../../cml/src/mountain.rs)).

**Consequence.** No structural metadata is stored. A snapshot is
`(n, root, seal)`. Version `n` is the prefix `nodes[0 .. nodes(n))`.

### §3. Measures, Folds, and List Homomorphisms

**Definition 3.1 (measure).** For a monoid `(M, ⊕, ε)`, a measure is a
function `μ : Claim → M`.

**Definition 3.2 (range summary).**
`Σ_μ[a, b) = μ(c_a) ⊕ μ(c_{a+1}) ⊕ … ⊕ μ(c_{b−1})`, with `Σ_μ[a, a) = ε`.

**Lemma 3.3 (split).** For `a ≤ m ≤ b`,
`Σ_μ[a, b) = Σ_μ[a, m) ⊕ Σ_μ[m, b)`. *Proof.* Associativity of `⊕`. ∎

**Definition 3.4 (list homomorphism).** `h : Log → A` is a list homomorphism
if there is an associative `⊙` on `A` with `h(xs ++ ys) = h(xs) ⊙ h(ys)`.
Equivalently `h = f ∘ Σ_μ` for some monoid `M`, measure `μ`, and finalizer
`f : M → A` — up to the choice of `A` being the image, `f` may be taken as
identity.

**Theorem 3.5 (third homomorphism theorem; Gibbons 1996).** If `h` is
computable as a leftward fold and as a rightward fold — there exist `⊳`, `⊲`
with `h(x : xs) = x ⊳ h(xs)` and `h(xs ++ [x]) = h(xs) ⊲ x` — then `h` is a
list homomorphism.

This is the operational test for whether a query is in the served class.

### §4. The Served Query Class

**Definition 4.1.** `Q_fold` is the set of queries `q : Range → A` of the
form `q[a, b) = f(Σ_μ[a, b))` for some `(M, μ, f)`.

**Lemma 4.2 (dyadic decomposition).** Any `[a, b) ⊆ [0, n)` is the disjoint
union of at most `2·⌈log₂ n⌉` intervals, each the leaf span of a perfect
subtree present in the MMR at size `n`. *Proof.* Standard segment-tree
decomposition into aligned dyadic blocks `[j·2^h, (j+1)·2^h)`. Every such
block with `(j+1)·2^h ≤ n` is a complete perfect subtree of the MMR at size
`n`, because a perfect subtree is permanent once complete. ∎

**Theorem 4.3 (cost).** If `Σ_μ` is available at every perfect-subtree
span, then any `q ∈ Q_fold` over any range costs `O(log n)` summary reads
and `O(log n)` applications of `⊕`, independent of `b − a`.
*Proof.* Lemmas 3.3 and 4.2. ∎

**Theorem 4.4 (closure).** `Q_fold` is closed under

- **products**: `(M₁ × M₂, ⊕ pointwise, (ε₁, ε₂))` is a monoid, so a tuple of
  queries is a query;
- **post-composition**: `g ∘ f ∘ Σ_μ` for any `g`;
- **restriction by kind**: setting `μ(c) = ε` for non-participating kinds.

*Proof.* Each is immediate from the definitions. ∎

**Proposition 4.5 (negative).** Queries that are not list homomorphisms —
order statistics such as the median, and joins on attributes with no
monoidal summary — are not in `Q_fold`, and no annotation of a
sequence-shaped Merkle tree serves them in `o(n)` without an external
index. *Argument.* Any subtree-level acceleration is a grouping of the
computation over the leaves; correctness under all groupings is
associativity, which these lack.

**Proposition 4.6 (point lookup).** Lookup by identity is not served by
the sequential shape. It is served by a keyed tree whose shape is a function
of its key set (§6) with `O(log n)` per lookup.

### §5. The Corroboration Monoid

**Definition 5.1 (symmetric corroboration).**
`C = 𝒫(Ref) × 𝒫(Ref)`, elements `(F, O)` read as *facts asserted* and
*obligations outstanding*, with

```
(F₁, O₁) ⊕ (F₂, O₂) = (F₁ ∪ F₂, (O₁ ∪ O₂) − (F₁ ∪ F₂))
ε = (∅, ∅)
```

**Theorem 5.2.** `(C, ⊕, ε)` is a commutative monoid.
*Proof.* Facts combine by union. For obligations, by induction any grouping
of `x₁ ⊕ … ⊕ x_m` yields `(⋃Oᵢ) − (⋃Fᵢ)`: the base case is the definition;
if two groups yield `(⋃O_L − ⋃F_L)` and `(⋃O_R − ⋃F_R)`, their combination's
obligation set is `((⋃O_L − ⋃F_L) ∪ (⋃O_R − ⋃F_R)) − (⋃F_L ∪ ⋃F_R)`, which
equals `(⋃O_L ∪ ⋃O_R) − (⋃F_L ∪ ⋃F_R)` because subtracting the full fact
union absorbs the inner subtractions. Identity and commutativity are
immediate. ∎

**Definition 5.3 (measure).** For a claim `c` with asserted references
`facts(c)` and dependency references `deps(c)`:
`μ_C(c) = (facts(c), deps(c) − facts(c))`.

**Definition 5.4 (corroborated).** Claim `c_i` is corroborated at size `n`
iff `deps(c_i) ∩ O = ∅` where `(F, O) = Σ_{μ_C}[0, n)`; equivalently
`deps(c_i) ⊆ F`.

**Definition 5.5 (causal corroboration).** Same carrier, with

```
(F₁, O₁) ⊕_c (F₂, O₂) = (F₁ ∪ F₂, O₁ ∪ (O₂ − F₁))
```

Only facts from the *earlier* operand discharge the later operand's
obligations.

**Theorem 5.6.** `(C, ⊕_c, ε)` is a (non-commutative) monoid.
*Proof.* Facts as before. Obligations:
`(x ⊕_c y) ⊕_c z` gives `O₁ ∪ (O₂ − F₁) ∪ (O₃ − (F₁ ∪ F₂))`;
`x ⊕_c (y ⊕_c z)` gives `O₁ ∪ ((O₂ ∪ (O₃ − F₂)) − F₁)
= O₁ ∪ (O₂ − F₁) ∪ (O₃ − (F₁ ∪ F₂))`. Equal. ∎

The symmetric monoid answers "is everything `c` needs present anywhere in
the log"; the causal monoid answers "was everything `c` needs present
*before* `c`". Both are in `Q_fold` (Definition 4.1); the choice is a
claim-algebra decision, not a structural one.

**Remark 5.7 (unboundedness).** `|F|` and `|O|` are `O(n)` in the worst
case. Boundedness is recovered by §8, not by the monoid.

### §6. Summary Claims

**Definition 6.1.** A summary claim is a claim of kind `Summary` with
payload `(M, [a, b), R, s)`: a named monoid, a range, the log root at some
size `≥ b`, and an asserted value `s ∈ M`. Its references are
`deps = {R}`; it asserts nothing else.

**Definition 6.2 (validity).** A summary claim is valid iff
`s = Σ_μ[a, b)` computed over the leaves committed by `R`.

**Theorem 6.3 (self-application).** Validity of a summary claim is
decidable by replay of `[a, b)` against `R`, and a valid summary claim is
corroborated in the sense of Definition 5.4 as soon as `R` is a committed
root. *Proof.* `R` commits the leaves of `[a, b)` (inclusion); replay
computes `Σ_μ[a, b)` deterministically; `deps = {R}` is discharged by the
seal that asserts `R`. ∎

Summary claims are therefore *reproducible claims* under the same trust
algebra as the claims they summarise. Their author is attributable, their
correctness is mechanically checkable, and trust in them factors through
trust in `R`.

**Discovery.** Summary claims are located by key `(M, [a, b))` in a keyed
tree derived deterministically from the log — a Merkle Search Tree or
prolly tree, whose shape is a function of its key set and which therefore
needs no structural metadata either. Its root at size `n` is a function of
the prefix and may be committed alongside. A range query for `M` over
`[a, b)` issues the `O(log n)` dyadic keys of Lemma 4.2.

**Evolvability.** A new monoid is a new `M` in summary payloads. Nothing in
§2 changes.

### §7. The Interior Pruning Signal

**Definition 7.1.** `P = (ℕ, +, 0) × (Sketch, ∪, ∅)`: a leaf count and a
set sketch (e.g. a Bloom filter of fixed width) of every `Ref` referenced by
claims in the subtree.

`P` is fixed at design time, computed along the carry path on append, and
bagged over the peaks by the same associative fold as the digests
([`cml::mountain::bag_peaks`](../../cml/src/mountain.rs)). Associativity is
the only property the bag requires; commutativity is not needed because the
bag order is fixed.

**Placement choice.** If `P` enters the hash preimage, prune results are
authenticated by the root and the preimage of the structural node changes.
If `P` is a sidecar keyed by position, roots are untouched and `P` is
rebuildable from the prefix. The polydigest combinator's metaroot offers a
third placement: a summary digest over the same leaf sequence as an
additional bound root. Which of the three applies is a decision for the
combinator's contract, not this model.

### §8. Boundedness and Locality

**Definition 8.1 (bounded summary).** `M` is bounded if `|m| ≤ B` for all
reachable `m`, for a constant `B` independent of `n`.

**Definition 8.2 (w-local).** A log is `w`-local for `μ_C` if, for every
claim `c_i`, every `r ∈ deps(c_i)` that is ever discharged is discharged by
some `c_j` with `|i − j| ≤ w`.

**Proposition 8.3.** In a `w`-local log, every *eventually discharged*
obligation in the `Σ_{μ_C}` summary of a perfect subtree of span `> 2w`
originates in one of its outermost `w` leaves on each side. *Proof.* An
eventually discharged obligation from an interior leaf is discharged within
`w`, hence inside the subtree, hence subtracted. ∎

Locality says nothing about obligations that are *never* discharged: a
permanently dangling dependency stays in every summary that contains it.
So under locality the exact corroboration summary of a large subtree is
`O(w + d)` where `d` is the number of permanently undischarged obligations
in the subtree, and pruning is exact. If `d` is not bounded — the algebra
permits claims whose dependencies never arrive — the exact summary is
unbounded and pruning must go through a sketch (§7), which is approximate:
a sketch miss proves absence; a sketch hit requires descent or a keyed
lookup.

Locality is a property of how the claim algebra emits claims. It is the
lever that turns a correct fold into a cheap one.

### §9. Succession Under Lease

**Definition 9.0 (position-qualified reference).** In this section a
reference is `ref(c) = (pos(c), digest(c))`. Resolving it is one array read
at `pos(c)` and one digest comparison; a reference whose digest does not
match the leaf at its position is invalid. No hash-to-position lookup is
required anywhere in this section.

**Definition 9.1 (succession chain).** A chain with origin `X` is a sequence
of claims `c₀ = X, c₁, …, c_m` where each `c_{j+1}` carries
`predecessor(c_{j+1}) = ref(c_j)` and `origin(c_{j+1}) = ref(X)`, and the
link `c_j → c_{j+1}` is legitimate under the trust algebra (e.g. signed by
the key `c_j` introduced).

**Definition 9.2 (lease).** A global constant `L_max ∈ ℕ` in leaf index.
Each `c_j` declares `L_j ≤ L_max`. The chain is **alive** at size `n` iff
`pos(c_{j+1}) < pos(c_j) + L_j` for every link and `n < pos(c_m) + L_m`.
Otherwise it is **expired** at the first violated bound.

**Theorem 9.3 (window).** If the chain of `X` is alive at `n`, then
`pos(c_m) ∈ [n − L_max, n)`. *Proof.* `n < pos(c_m) + L_m ≤ pos(c_m) + L_max`.
∎

**Corollary 9.4 (provable absence).** If no claim with `origin = X` has
position in `[n − L_max, n)`, the chain of `X` is expired at `n`. The
statement is a range predicate over a bounded window and is therefore in
`Q_fold` with the same cost as any range query; if the window summaries are
committed (§7), the negative is authenticated.

**Definition 9.5 (succession monoid).**
`S = Map⟨Ref, ℕ × Ref⟩`, mapping an origin to `(pos, ref)` of a claim in
the range, with `⊕` = key-wise union choosing the entry of greater `pos`,
and `ε = ∅`. Measure: `μ_S(c) = {origin(c) ↦ (pos(c), ref(c))}` for
rotation claims, `ε` otherwise.

**Theorem 9.6.** `(S, ⊕, ε)` is a commutative monoid, and
`|Σ_S[a, b)| ≤ b − a`. *Proof.* Key-wise max over a total order is
associative and commutative; each leaf contributes at most one key. ∎

**Theorem 9.7 (bounded forward query).** "Current successor of `X` at `n`"
is `Σ_S[n − L_max, n)(X)`, computed in `O(log L_max)` summary reads each of
size `≤ L_max`. *Proof.* Theorem 9.3 locates the answer in the window;
Lemma 4.2 decomposes the window into `O(log L_max)` perfect-subtree spans
each of span `≤ L_max`; Theorem 9.6 bounds each summary. ∎

Summaries of `S` need only be materialised for spans `≤ L_max`; no query
reads a larger one.

**Proposition 9.8 (verification is a link walk).** Verifying that the
claim returned by Theorem 9.7 is in the chain of `X` is a walk of its
`predecessor` references back to `X`: `m` hops, each one array read, one
digest comparison, and one link-legitimacy check. It is never a scan, and
under Definition 9.0 it touches no structure other than the node and leaf
arrays.

**Proposition 9.8a (walk length).** `m ≥ (n − pos(X)) / L_max`, because
the lease forces a renewal at least every `L_max` leaves. A cold
verification is therefore linear in the chain's age. This is inherent — the
links are independent signatures — and is amortised by a **chain
checkpoint**: a summary claim (§6) with payload `(X, c_j, R)` asserting the
chain of `X` is valid through `c_j` under root `R`, reproducible by
replaying the walk. After a checkpoint, verifying the current successor is
one link plus one checkpoint.

**Remark 9.9 (forks).** Two claims with the same `predecessor` are
detectable by the count monoid over `(origin, predecessor)`; resolution
(first-wins, causal, or rejection) is a claim-algebra policy, not a
structural one.

**Remark 9.10 (wall-clock leases).** If leases are to be expressed in time,
a `(max timestamp, max)` component in the interior signal `P` translates a
time bound to a position bound by `O(log n)` descent. The structural
statement of this section is unchanged; only the window's endpoint is
computed differently.

**Remark 9.11 (generality).** Any "current value of `X`" query — revocation,
ownership transfer, record updates — is succession under lease. A derived
keyed tree (§6) also answers it in `O(log n)` with a non-membership proof,
but "latest ever" is not "currently valid": the lease is what supplies
liveness, bounds the summaries, and keeps the query on the log's own
structure.

### §10. Worst-Case Complexity

Parameters: `n` log size; `B` summary bound; `L = L_max`; `w` locality
window; `d` permanently undischarged obligations; `m` chain length; `K`
live succession chains; `r` result size; `q` monoid components in the
product; `|deps|` references per claim. Arity `k` is a constant.

**Per component.**

| Component                           | Operation                 | Worst case                                   | Notes                                                          |
| :---------------------------------- | :------------------------ | :------------------------------------------- | :------------------------------------------------------------- |
| Shape (§2)                          | position, peaks, path     | `O(log n)`                                   | input-independent; worst equals typical                        |
| Shape                               | append                    | `O(log n)` worst, `O(1)` amortised           | carry cascade at `n = 2^h − 1`                                 |
| Shape                               | root, inclusion, consist. | `O(log n)`                                   |                                                                |
| Shape                               | snapshot                  | `O(1)`                                       | `(n, root, seal)`                                              |
| Interior signal `P` (§7)            | append                    | `O(B log n)` worst, `O(B)` amortised         | recompute along the carry path                                 |
| Interior signal `P`                 | prune, span `≤ L`         | effective                                    | sketch sized for `L`                                           |
| Interior signal `P`                 | prune, global             | `Θ(n / S_sat)` — linear                      | fixed-width sketch saturates above span `S_sat`                |
| Fold query, bounded `M` (§4)        | range                     | `O(qB log n + r)`                            | the designed case                                              |
| Fold query, unbounded `M`           | range                     | `O(n)`                                       | do not materialise above a span cap                            |
| Summary materialisation             | storage                   | `O(n log B)` bounded, `O(n log n)` unbounded | all dyadic levels                                              |
| Corroboration, per claim, causal    | check `c`                 | `O(|deps|)`                                  | position-qualified refs: one read per dep; no fold             |
| Corroboration, per claim, symmetric | check `c`                 | `O((w + d) log n)` local; `O(n)` non-local   | forward-pending deps cannot be position-qualified              |
| Corroboration, aggregate            | uncorroborated in range   | `O((w + d) log n)` local; `O(n)` non-local   |                                                                |
| Succession (§9)                     | lookup, absence           | `O(log L)` probes                            | one origin; `O(L)` for all live chains                         |
| Succession                          | verify, cold              | `O(m)`, `m ≥ age / L`                        | `O(n)` for a chain rotating every leaf                         |
| Succession                          | verify, checkpointed      | `O(1)` + distance since checkpoint           |                                                                |
| Succession                          | write amplification       | `K / L` renewals per leaf                    | the hidden cost                                                |
| Derived keyed tree (§6)             | lookup                    | `O(log n)` w.h.p.                            | hash-derived shape; unbalancing requires grinding              |
| Derived keyed tree                  | rebuild; incremental      | `O(n log n)`; `O(log n)`                     |                                                                |
| Summary-claim replay (§6)           | verify one summary        | `O(span · B)`                                | inherent to reproducibility                                    |
| Signatures                          | per claim, per link       | `O(1)`                                       |                                                                |

**Composition.**

- **Append** is `O(log n · (1 + qB))` worst and `O(qB)` amortised. Storage
  is linear in every component: `2n` digests, `n` payloads, `n log B`
  summaries, `n` keyed-tree nodes. Nothing is superlinear in storage.
- **Every operation the design intends** is polylogarithmic in `n` with
  constants `B`, `L`, `w`, `d`, `|deps|`: fold queries `O(qB log n + r)`,
  succession `O(log L)`, point lookup `O(log n)`, causal corroboration
  `O(|deps|)`.
- **Every operation outside the design degrades to `O(n)` per operation
  and never worse.** The `O(n log n)` entries are batch rebuilds.
- **The overall per-operation worst case is `O(n)`**, reached through
  exactly four doors: a non-homomorphic query (Proposition 4.5); an
  unbounded summary read at large span (Remark 5.7); sketch-only global
  lookup (§7); cold verification of a chain that rotated at every leaf
  (Proposition 9.8a). All four are decidable from the algebra at design
  time.

**Observation 10.1 (causal corroboration needs no fold).** With
position-qualified references (Definition 9.0), checking a single claim
under the causal monoid is `O(|deps|)` — resolve each reference, verify the
digest, verify the link. The fold is required only for aggregate questions
and for the symmetric monoid, where an obligation may be discharged by a
*later* claim and therefore cannot carry a position. Locality and `d`
constrain that narrower set.

**Shapes that do not fit.**

1. **Joins and order statistics.** `O(n)`; an external index is required
   and the model cannot hide it.
2. **Many live chains relative to the lease.** Renewals cost `K / L`
   writes per leaf; at `K > L` the log is mostly renewals. The trade is
   expiry latency (`≤ L`) against write amplification (`K / L`). Fits
   registries where live keys `≪ L`; does not fit high-churn short-lived
   sessions with fast expiry.
3. **Non-local symmetric corroboration at scale.** Unbounded pending
   obligations make `d` unbounded and aggregate queries `O(n)`. Fits
   provenance where inputs precede outputs; does not fit an unbounded
   pending-review backlog unless the backlog is itself leased.
4. **High-cardinality global point lookup without the derived tree.**
   Linear. Fits once the derived keyed tree is accepted as a cache with a
   committed root.
5. **Constant-latency appends.** Appends are `O(log n)` at `2^h`
   boundaries, not `O(1)`.

Registries, provenance, attestations, revocation, and ownership records
are causal, local, and have `K ≪ L`; they land in the polylogarithmic
column throughout.

#### §10.2. Under the Algebra's Guarantees

Assume the claim algebra — itself a formal object with its own proofs —
guarantees that no operation passes through the four `O(n)` doors: every
monoid it uses is bounded by `B` **at every dyadic level**; corroboration is
causal, or `w`-local with bounded `d`; a global `L_max` holds; chain
checkpoints occur at least every `c` links; point lookup goes through the
derived keyed tree; and no non-homomorphic query is issued. Use cases that
cannot meet these are not tracked in the structure, so the assumption is
self-selecting.

**Theorem 10.2.1 (Merkle floor).** Under these guarantees every operation
is `O(log n)` worst case in `n`, and the `log n` is exactly the height of
the Merkle commitment. The query layer adds no factor of `n`.

| Operation                                  | Worst case in `n`                              | Source of the bound                       |
| :----------------------------------------- | :--------------------------------------------- | :---------------------------------------- |
| append                                     | `O(log n)` worst, `O(1)` amortised             | carry cascade                             |
| any fold query, any range                  | `O(log n)`                                     | Lemma 4.2; summaries exist at every level |
| succession lookup, provable expiry         | `O(1)` in `n` — `O(log L)`                     | Theorem 9.7; window independent of `n`    |
| chain verification, checkpointed           | `O(1)` in `n` — `O(c)`                         | checkpoint discipline                     |
| causal corroboration of one claim (holder) | `O(1)` in `n` — `O(                            | deps                                      |
| point lookup                               | `O(log n)`                                     | derived keyed tree                        |
| any operation, remote verifier             | `+ O(log n)` per leaf; `O(r log(n/r))` batched | inclusion proofs against a root           |
| storage                                    | `O(n)`                                         |                                           |
| total work to build                        | `O(n)` amortised; `O(n log n)` keyed tree      | the latter is the sort bound              |

*Proof sketch.* Each row is the corresponding entry of the component table
with the unbounded parameters replaced by the algebra's constants. The
all-levels requirement is what keeps arbitrary ranges at `O(log n)`: a
summary span cap `S_max` would make a whole-log query read `n / S_max`
blocks, which is linear. The succession monoid is exempt because it is only
queried on windows `≤ L`. ∎

**Corollary 10.2.2 (optimality).** An inclusion proof in a balanced Merkle
tree over `n` leaves requires `Ω(log n)` digests, so `Θ(log n)` per
authenticated operation is the floor for any authenticated structure; the
build bound `O(n log n)` for the keyed tree is the comparison-sort floor
for an ordered authenticated key set. The design meets both.

**Remark 10.2.3 (where the constants go).** `B`, `L`, `w`, `d`, `|deps|`,
`q`, `c`, and the renewal amplification `K / L` multiply the constant or
inflate `n` itself (renewals are leaves). None enters the exponent. The
tree owns the `log n`; the algebra owns the constants.

### §11. Theorems and Corollaries

- **T1 (shape sufficiency).** `n` determines every position, peak, and
  path of the log (§2). No structural metadata is stored.
- **T2 (served class).** The log serves a query without an external index
  iff the query is a list homomorphism (§3–4).
- **T3 (cost).** Every served query costs `O(log n)` summary reads per
  range (Theorem 4.3).
- **T4 (closure).** The served class is closed under products,
  finalizers, and kind-restriction (Theorem 4.4).
- **T5 (corroboration).** Symmetric and causal corroboration are list
  homomorphisms (Theorems 5.2, 5.6).
- **T6 (self-application).** Summary claims are reproducible claims under
  the same trust algebra (Theorem 6.3).
- **T7 (locality).** Exact subtree summaries are `O(w + d)` in a
  `w`-local log with `d` permanently undischarged obligations
  (Proposition 8.3).
- **T8 (succession).** Under a global lease `L_max`, the current successor
  of any origin is a bounded backward range query costing `O(log L_max)`
  reads of summaries of size `≤ L_max`, and expiry is provable absence
  (Theorems 9.3–9.7, Corollary 9.4).
- **N1 (limits).** Non-homomorphic queries and cross-attribute joins are
  not served; point lookup routes through the derived keyed tree
  (Propositions 4.5, 4.6).
- **N2 (walk length).** Chain verification is a link walk of `m` hops,
  never a scan, but `m ≥ age / L_max` under the lease; amortised to one
  link plus one checkpoint by chain checkpoint claims (Propositions 9.8,
  9.8a).

### Validation

Each claim above has a falsification signpost.

| Claim | Falsified if                                                                                     |
| :---- | :----------------------------------------------------------------------------------------------- |
| T1    | Any proof or root computation needs data other than `n` and the node array                       |
| T2    | A query passes the two-fold test of Theorem 3.5 yet no associative `⊕` exists                    |
| T3    | A range decomposes into more than `2·⌈log₂ n⌉` perfect-subtree spans                             |
| T5    | A property test finds `(x ⊕ y) ⊕ z ≠ x ⊕ (y ⊕ z)` for either monoid                              |
| T6    | Replay of a valid summary's range against `R` yields `≠ s`                                       |
| T7    | A `w`-local corpus yields a subtree summary with `> 2w + d` obligations                          |
| T8    | An alive chain has no renewal in `[n − L_max, n)`, or a span-`s` `S` summary exceeds `s` entries |

Property tests for T5 are cheap and should exist before any monoid is
adopted into the algebra: generate random `(F, O)` triples and check
associativity for `⊕` and `⊕_c`, and commutativity for `⊕` only.

### Implications

- **For the claim algebra.** Every query kind the algebra intends to
  support must ship its `(M, ⊕, ε, μ, f)`, a bound or sketch for `|M|`, and
  a locality expectation. Queries that fail the two-fold test are outside
  the design and need an explicit, external index — which should be said,
  not discovered. Succession-shaped state needs position-qualified
  `origin` and `predecessor` references on every update and a global
  `L_max`.
- **For the log.** No change to the spine, the bag, or the proof corpus is
  required for summary claims. The interior signal `P` is the one
  structural addition, and its placement (preimage, sidecar, or polydigest
  slot) is a separate decision.
- **For storage.** The positional `Storage` trait already has the right
  shape; a flat post-order file is its purest backend. The derived keyed
  tree is a cache with a committed root, rebuildable in `O(n log n)` and
  maintained in `O(log n)` per append.

### References

- Bird, R. *An Introduction to the Theory of Lists*. In Logic of
  Programming and Calculi of Discrete Design, 1987. — list homomorphisms.
- Gibbons, J. *The Third Homomorphism Theorem*. Journal of Functional
  Programming 6(4), 1996. — the two-fold test (Theorem 3.5).
- Hinze, R. and Paterson, R. *Finger Trees: A Simple General-purpose Data
  Structure*. Journal of Functional Programming 16(2), 2006. — monoidal
  measures on tree structure.
- Auvolat, A. and Taïani, F. *Merkle Search Trees: Efficient State-Based
  CRDTs in Open Networks*. SRDS 2019. — keyed trees whose shape is a
  function of the key set.
- Todd, P. *Merkle Mountain Ranges*. OpenTimestamps, 2012. — the
  positional layout of §2.
