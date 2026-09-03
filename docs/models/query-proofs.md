# MODEL: Query Proofs

<!--
  Formal domain model generalising inclusion and consistency proofs over an
  append-only Merkle log to *query proofs*: verifiable evidence that a fold
  over the committed log evaluates to a stated answer, checkable in
  O(log n). Establishes the outcome trichotomy (an answer, a violation, or
  a malformed witness), timestamp-boundary proofs, the k·log n
  honest-record proof, and the monotone boundary beyond which no query
  proof can reach — the line that separates the record layer from the
  liveness layer above it.
-->

**Audience.** Engineers and formal-methods readers designing protocols on
top of the append-only Merkle log. This model builds directly on the
[fold-closed claim log](fold-closed-log.md); its definitions — measure,
fold, dyadic block, lease, provable absence — are used here without
restatement. Familiarity with inclusion and consistency proofs is assumed.

**Answer.** A **query proof** is the verifiable form of a fold: evidence
that query `q` over the log committed by `(n, R)` evaluates to answer `v`,
checkable in `O(log n)` by a verifier holding only the commitment.
Inclusion and consistency proofs are its two content-free instantiations,
so the log's existing proof vocabulary is a special case, not a sibling.
A query proof's outcome is three-valued — a proven answer (absence
included), a witnessed violation, or a malformed witness — and only the
middle one ever indicts the record. If every load-bearing rule of a
protocol is expressible as a query proof, the record proves its own
honesty in `O(k log n)` with no trusted intermediary. The hard boundary is
**monotonicity**: a query proof establishes exactly the properties of a
committed prefix, which are stable under extension — so it can never
establish that a commitment is *current*. Tip currency, and with it
equivocation detection, provably belongs to a **liveness layer** above the
record: a proof of possession bounded by a protocol time resolution.

---

## Part I — Plain reading

### Three proofs, one type

An append-only Merkle log ships with two famous proofs. An **inclusion
proof** shows a particular leaf sits at a particular position. A
**consistency proof** shows an older log is a prefix of a newer one. Both
have the same anatomy: the verifier holds only a root, the prover sends
`O(log n)` hashes, the verifier recombines them and compares.

The [fold-closed model](fold-closed-log.md) established which queries the
log can serve without an external index: exactly the list homomorphisms —
a monoid-valued measure per leaf, an associative combine, a finalizer. A
**query proof** is what makes such a query *verifiable* rather than merely
computable: evidence that the fold over the committed log yields the
stated answer. Inclusion is the point query ("the value at position `i`"),
consistency is the prefix query ("`(n', R')` summarises positions
`[0, n')`"), and both need no measure beyond the digest itself — which is
why they came for free before anyone asked for a general theory. The
general theory says: every homomorphic query gets a proof of the same
shape and the same cost.

### What a witness contains

Associativity lets a fold be bracketed along the tree's own subtrees. Any
queried range splits into `O(log n)` **dyadic blocks** — maximal perfect
subtrees. The witness for a query proof is: the block summaries for that
decomposition, plus the Merkle paths binding each block to the root. The
verifier authenticates each block, combines the summaries with the
query's own `⊕`, applies the finalizer, and compares against the claimed
answer. Verification is `O(log n)` summary combines and `O(log n)` hashes.

The prover may compute its side however it likes — cached interior
summaries, brute scan, an index nobody else trusts. The witness is
self-contained; the prover's method never enters the trust argument.

### Failure is an answer

A recurring state of any real query is "nothing found", and the type must
handle it without ceremony. Because a query's answer is a monoid value,
emptiness is a value like any other. The outcome of checking a query
proof is three-valued:

- **Proven(v)** — the fold provably yields `v`, where `v` may itself be
  "absent", "empty", or "expired". Provable absence (the lease result of
  the fold-closed model) is a *positive* answer, and the most common one.
- **Violation witnessed** — the query targets a protocol invariant and the
  authenticated answer exhibits a breach. The combine can be built to
  carry the leftmost offending pair, so the proof pinpoints an
  authenticated counterexample. Only this outcome indicts the record.
- **Malformed witness** — the hashes do not authenticate against the
  root. This indicts the *prover* and says nothing about the record.

A client that sends a bad proof has told you about itself, not about the
log. The trichotomy keeps those two accusations rigorously apart.

### Finding a moment in the log

Leases in the fold-closed model bound succession searches by *leaf
count*. Humans think in time. The bridge is one invariant: **timestamps
never decrease along the log**. Grant that, and "which position
corresponds to time `t`?" is a predecessor search over a sorted sequence,
with three constructions:

1. **Binary search** over leaves, each probe an inclusion proof:
   `O(log² n)`, zero new machinery.
2. **Adjacent-pair proof**: the prover exhibits *neighbouring* leaves
   `i, i+1` with `ts_i ≤ t < ts_{i+1}` and their two inclusion proofs.
   Sortedness makes adjacency conclusive — nothing else can sit between
   them — so one `O(log n)` witness pins the boundary. This is the
   standard sorted-Merkle-tree absence trick.
3. **Annotated descent**: max-timestamp in the interior pruning signal
   turns the search into one root-to-leaf walk, `O(log n)` with the best
   constants, at the cost of the annotation infrastructure.

A timestamp lease is then a counter lease plus one boundary proof: resolve
`t_expiry` to a position, run the same bounded window check from there.
One extra logarithmic term buys the human-legible expiry.

### Proofs that depend on proofs

Constructions 2 and 3 are sound *only if the ordering invariant actually
holds*. A log with one backward timestamp makes "adjacent" meaningless
for boundary-finding. And "are all timestamps ordered?" is itself a
homomorphic query — the textbook one — so the invariant has its own query
proof.

Query proofs therefore form a **dependency hierarchy**: invariant proofs
at the bottom, queries whose soundness assumes those invariants above
them. This is not a weakness to engineer around; it is the load-bearing
structure the honest-record proof below makes explicit.

### Proving the whole record honest

A protocol is a set of rules over the record. Sort them by how a query
proof can reach them:

- **Per-leaf rules** — well-formedness, signature validity. A valid-bit
  measure; trivially homomorphic.
- **Neighbour rules** — timestamp ordering, append-only counters.
  Homomorphic with boundary carrying: measure `(first, last, ok)`,
  combine checks the junction.
- **Backward-reference rules** — each entry links the state it extends; a
  rotation names its predecessor; a key must be unrevoked at use. Checked
  per entry through position-qualified references; the whole-record
  certificate is built *incrementally* as the log grows, checkpoint by
  checkpoint, rather than by one fold.
- **Keyed rules** — uniqueness within the log (no nonce replay, no
  duplicate name). Not a positional fold; they need the derived keyed
  tree as a committed index, itself a pure function of the log and
  therefore auditable. Note the scope: uniqueness *within this log*.
  Cross-log uniqueness is a claim about the world, which is the next
  class.
- **World rules** — delivery obligations, wall-clock accuracy, "the view
  you were shown is the only view". Not expressible as query proofs even
  in principle. These are not about the record.

Everything except the last class is reachable. If the load-bearing rules
of a protocol number `k` and all fall in the first four classes, then
**`k` query proofs at `O(log n)` each prove the record obeys every
internal rule, relative to its root, with no trusted intermediary**. The
verifier's honest price: `O(k log n)` is the *incremental* cost, paid
against a previously trusted root; a verifier trusting nothing but
genesis pays one linear audit first, or accepts attributed summary claims
under the trust algebra itself.

### The edge of the record: liveness

One thing no query proof will ever deliver: that the root you verified
against is the *current* one. The reason is structural, not a missing
trick. Everything a query proof establishes is a property of a committed
prefix, and prefix properties are **monotone** — once true of the prefix,
they stay true no matter what is appended after. "This root is the tip"
is the opposite kind of statement: the very next append falsifies it. A
proof technique whose conclusions are permanent cannot establish a
property that expires.

So equivocation — one identity, two irreconcilable views — sits strictly
above the record, in a **liveness layer**, and this is a clean separation
of concerns rather than a gap. The trust trichotomy of the factoring-trust
work states the general form: currency of a tip requires a live holder to
assert it. The instrument is a **proof of possession (PoP)**: a signed
claim binding the current time, the current tip, the subject, and the
asserting key, valid only within a protocol-level **time resolution** —
older than the resolution, it proves nothing about *now*. The asymmetry
between the layers is exact: record-layer findings are *affirmable*
(divergence, once proven, is permanent evidence), while liveness is only
*refutable* (any number of consistent checks is compatible with a
conflict at the next one). A PoP can convict a tip of staleness; it can
never certify honesty forward.

### What this buys: bounded partial sync

Put the layers together and partial sync stops being a compromise. A
client that holds only the commitment `(n, R)` — no leaves — and receives
query proofs for the `k` load-bearing rules has verified protocol honesty
of the entire prefix in `O(k log n)`. Add one PoP fresher than the time
resolution and the client's view is honest *and* current-within-resolution.
Nothing about safety required holding the chain. Full replicas remain
useful for serving proofs and for the one-time cold audit — but holding
data is now an *availability* role, not a *trust* role.

---

## Part II — Formal model

### Domain Classification

- **Domain.** Verifiable computation over authenticated append-only
  structures: proofs that a declared function of a committed log equals a
  declared value.
- **In scope.** The query-proof type and its verification cost; the
  outcome trichotomy; ordered-time boundary proofs; composition into a
  whole-record honesty proof; the monotone boundary and its consequence
  for liveness.
- **Out of scope.** The liveness layer's own internals (gossip topology,
  witness selection, PoP transport); the claim algebra's contents; fork
  *resolution* policy. The equivocation-detection architecture of the
  consuming protocol treats those.

### Formalism Selection

The model continues the algebraic setting of the
[fold-closed claim log](fold-closed-log.md): monoid-valued measures and
list homomorphisms over the MMR positional structure. The one new
ingredient is an explicit stability (monotonicity) argument over log
extension, used to delimit what the proof type can express. No category
theory is required.

### §1. Setting

Carried unchanged from the fold-closed model: the log `L = [c₀ … c_{n−1}]`
with commitment `(n, R)`; measures `μ : Claim → M` into monoids
`(M, ⊕, ε)`; the served class `Q_fold` of list homomorphisms; dyadic
decomposition of any range `[a, b) ⊆ [0, n)` into `O(log n)` complete
perfect subtrees; position-qualified references `(pos, digest)`; leases
and provable absence. `D` denotes the digest monoid: the measure whose
summary of a block is the block's Merkle digest.

### §2. Query Proofs

**Definition 2.1 (query proof).** Let `q ∈ Q_fold` with measure `μ`,
combine `⊕`, finalizer `f`, over range `[a, b)`. A **query proof** for
`q` against commitment `(n, R)` is a tuple `(v, W)` where `W` contains,
for each dyadic block `B₁ … B_m` of `[a, b)` (with `m ≤ 2·log₂ n`):

- the block summary `s_j = Σ_μ(B_j)`, and
- an authentication path binding `B_j`'s subtree digest to `R`,

such that `f(s₁ ⊕ … ⊕ s_m) = v`. The verifier accepts iff every path
authenticates and the recombination equals `v`.

For a summary to be checkable the block must be *openable*: either the
summary is the digest itself (`μ = D`), or the interior commits to the
summary (the pruning-signal placement of the fold-closed model, §7), or
the block is small enough to ship its leaves. Which of the three applies
is fixed per query kind at design time.

**Theorem 2.2 (verification cost).** Verifying a query proof costs
`O(log n)` combines in `M` plus `O(log n)` digest computations, against a
verifier state of one commitment. *Proof.* Dyadic decomposition bounds
`m`; each block contributes one combine and one path of length
`O(log n)`, but paths overlap so the total distinct hashes are
`O(log n)`; associativity of `⊕` makes the bracketing by blocks equal the
leaf-order fold. ∎

**Proposition 2.3 (inclusion is a point query proof).** The query
`q_i = "the leaf at position i"` with `μ = D` over range `[i, i+1)` has
as its query proof exactly the classical inclusion proof: the single
block is the leaf, its summary is the leaf digest, and the witness
degenerates to the authentication path. ∎

**Proposition 2.4 (consistency is a prefix query proof).** The query
`q_{n'} = "the digest summary of [0, n')"` with `μ = D` has as its query
proof exactly the classical consistency proof: the dyadic blocks of
`[0, n')` are the old log's peaks, their summaries recombine to `R'`, and
the paths bind them into `R`. Acceptance states `(n', R')` is a prefix of
`(n, R)`. ∎

**Remark 2.5 (the digest is the universal summary).** Every query proof
already carries digests — they are how blocks authenticate. Inclusion and
consistency are precisely the queries whose answer needs *nothing but*
the digests; every other query adds one more monoid on top of the
transport that was already there. This is why the two classical proofs
predate the general type: they are its `μ = D` fibre.

### §3. The Outcome Trichotomy

**Definition 3.1 (outcomes).** Checking a query proof yields exactly one
of:

- `Proven(v)` — all paths authenticate and recombination yields `v`;
- `Violation(w)` — as `Proven`, where `q` is an invariant query and `v`
  carries a witness `w` of breach;
- `Malformed` — some path fails to authenticate, or the recombination
  does not equal the claimed `v`.

**Proposition 3.2 (absence is Proven).** A proof of provable absence —
e.g. no renewal within a lease window — is `Proven(⊥)` for the relevant
query, not a failure mode. It indicts nothing and is the expected steady
state of most lease checks. ∎

**Definition 3.3 (violation-localising monoid).** For a neighbour
invariant `P` over adjacent leaves, define
`μ(c) = (first c, last c, None)` and let the combine check `P` at the
junction, recording `Some((pos_l, pos_r))` for the *leftmost* junction
that fails (first-failure semantics: `x ⊕ y` keeps `x`'s violation if
present, else the junction's, else `y`'s).

**Proposition 3.4.** The violation-localising combine is associative, and
`Violation` outcomes built from it carry an authenticated leftmost
counterexample — two positions whose leaves any party can open against
`R`. *Proof sketch.* First-failure selection over an ordered
concatenation is associative because leftmost-ness is; the interval
endpoints compose as in the ordering monoid. ∎

**Remark 3.5 (who is indicted).** `Malformed` is an accusation against
the prover only: nothing about the record follows from a witness that
fails to authenticate. Protocol handling of the two accusations must not
share a code path, or a buggy client becomes indistinguishable from a
dishonest record.

### §4. Time Boundaries

**Definition 4.1 (ordering invariant).** The log is **time-ordered** iff
`ts(c_i) ≤ ts(c_{i+1})` for all `i` — a neighbour invariant with the
ordering monoid `(first, last, ok)` and combine
`(f₁,l₁,ok₁) ⊕ (f₂,l₂,ok₂) = (f₁, l₂, ok₁ ∧ ok₂ ∧ l₁ ≤ f₂)`, associative
by inspection.

**Definition 4.2 (boundary query).** For time `t`, the boundary
`β(t) = max { i : ts(c_i) ≤ t }` (or `−1` if none).

**Constructions 4.3.** Three query-proof constructions for `β(t)`:

| Construction       | Witness                                     | Cost        | Needs                       |
| :----------------- | :------------------------------------------ | :---------- | :-------------------------- |
| (a) binary search  | one inclusion proof per probe               | `O(log² n)` | nothing new                 |
| (b) adjacent pair  | leaves `i, i+1` + two inclusion proofs      | `O(log n)`  | ordering invariant          |
| (c) annotated walk | one root-to-leaf descent over max-ts signal | `O(log n)`  | interior annotation + (4.1) |

**Theorem 4.4 (adjacent-pair soundness).** If the ordering invariant
holds on `[0, n)`, then authenticated adjacent leaves `i, i+1` with
`ts(c_i) ≤ t < ts(c_{i+1})` prove `β(t) = i`. *Proof.* Monotonicity gives
`ts(c_j) ≤ ts(c_i) ≤ t` for all `j ≤ i` and `ts(c_j) ≥ ts(c_{i+1}) > t`
for all `j > i`. ∎

**Remark 4.5 (conditional soundness and the hierarchy).** Theorem 4.4 is
*conditional* on Definition 4.1's invariant, which is itself query-provable
(it is the ordering monoid's own proof, with §3.3 localisation on
failure). Query proofs therefore form a dependency order: invariant
proofs are premises of boundary proofs, which are premises of
timestamp-lease proofs. A verifier caches invariant outcomes per root and
re-derives them per consistency step, so the premise costs amortise to
the incremental rate of §5.

**Corollary 4.6 (timestamp leases).** A lease expressed as a wall-clock
expiry `t_e` reduces to the leaf-count lease of the fold-closed model at
the cost of one boundary proof: resolve `β(t_e)`, then run the bounded
window check from that position. Asymptotics are unchanged; expiry
becomes human-legible. Expiry is judged in *log time*; the fidelity of
log time to wall-clock time is a liveness-layer concern (§6). ∎

### §5. The Honest-Record Proof

**Definition 5.1 (rule classes).** A protocol rule over the record is
classified:

| Class | Shape                      | Query-proof status                             |
| :---- | :------------------------- | :--------------------------------------------- |
| A     | per-leaf predicate         | homomorphic (valid-bit measure)                |
| B     | neighbour predicate        | homomorphic (boundary carrying, §4.1)          |
| C     | bounded backward reference | per-leaf check + incremental certificate       |
| D     | keyed (uniqueness in-log)  | derived keyed tree as committed index          |
| E     | world property             | not expressible; belongs to the liveness layer |

**Proposition 5.2 (class results).** (A), (B) are `O(log n)` query proofs
outright. (C) is `O(|deps| · log n)` per leaf via position-qualified
references; the whole-record certificate is maintained incrementally
under checkpoint discipline — each append extends it in `O(|deps| ·
log n)` — and is *not* a one-shot fold (its measure is not a function of
the leaf alone). (D) is `O(log n)` per query against the derived keyed
tree, whose root is a pure function of the log prefix and hence
auditable; scope is strictly per-log. ∎

**Theorem 5.3 (honest-record proof).** Let a protocol's load-bearing
rules be `K`, `|K| = k`, all in classes A–D. Then a verifier holding a
trusted root verifies, on each root transition, that the record satisfies
every rule in `K`, at total cost `O(k log n)` plus the consistency proof.
No party other than the prover of the witnesses is trusted, and the
prover is not trusted either — only the commitment is. *Proof.* Each rule
contributes one query proof (A, B, D) or one certificate extension check
(C); Theorem 2.2 bounds each at `O(log n)`; the consistency proof ties
the new root to the trusted one. ∎

**Definition 5.4 (verifier stances).** Theorem 5.3 prices the
*incremental* stance. Three legitimate stances, by initial trust:

- **cold audit** — trust only genesis: one `O(n)` replay, then
  incremental forever;
- **incremental** — trust a prior root: `O(k log n)` per transition;
- **attributed** — trust a summary claim by its signer under the trust
  algebra (the self-application result of the fold-closed model, §6):
  `O(k log n)` immediately, with trust reduced to attribution rather
  than to arithmetic.

A protocol should name which stance each party is expected to hold; the
three differ in trust, not in soundness of the proofs themselves.

**Remark 5.5 (scope of truth).** Class D deliberately stops at the log
boundary. Cross-log uniqueness — one name across all logs, one balance
across all holders — is a class E property: it is a claim about the
world's set of logs, not about any log. A protocol whose source of truth
is the log's own key-holder needs no such rule to be load-bearing; a
protocol that does need one (a currency needs "unspent *anywhere*") has
left the record layer and must buy network agreement. The classification
makes that purchase explicit instead of accidental.

**Remark 5.6 (certifying the derived index).** Class D's committed
index is kept honest *transitionally*, never by reconciliation. Three
requirements make staleness unreachable rather than detected: (i) the
keyed tree's shape is a pure function of its key set, so each key set
has exactly one root; (ii) that root is committed beside the log root;
(iii) each append's certificate carries the non-membership proof of the
new key against the previous root plus the insertion path yielding the
new one — `O(log u)` per key, `u` the live key count. Under (i)–(iii)
the maintenance proof and the uniqueness check are the same object — a
verifier never pays for them separately — and a published root that
disagrees with derivation is an attributable violation, not a drifted
cache. Requirement (i) is load-bearing: an insertion-order-dependent
tree admits two honest roots for one key set, and attribution collapses.

### §6. The Monotone Boundary

**Definition 6.1 (monotone property).** A property `P` of commitments is
**monotone** iff whenever `P` holds of `(n, R)` and `(n, R)` is a prefix
of `(n', R')`, the grounds for `P` remain valid: `P`'s truth about the
prefix `[0, n)` is unaffected by the extension.

**Theorem 6.2 (expressive boundary).** Every fact established by a query
proof is a monotone property of its commitment, and every `Q_fold` query
over a fixed range yields such a fact. *Proof.* A query proof's
conclusion quantifies only over `[a, b) ⊆ [0, n)`; appended leaves change
neither the leaves of the prefix nor its dyadic structure (peak
permanence), so the witness re-verifies unchanged against any extension's
view of the prefix. ∎

**Corollary 6.3 (no proof of currency).** "R is the current tip" is
falsified by the next append, hence non-monotone, hence outside the reach
of any query proof — not as a limitation of this construction but of any
proof whose conclusions are stable. Equivocation detection, which is the
comparison of two *current* claims, therefore cannot be built from query
proofs alone. ∎

**Definition 6.4 (proof of possession).** The liveness layer's instrument
is a **PoP**: a signed claim binding `(t_now, tip, subject, key)`, valid
only while `t_now` is within the protocol's **time resolution** `δ` of
the verifier's clock. A PoP older than `δ` proves possession *then*, not
*now*; the record may append a stale PoP as an ordinary historical claim,
but its liveness force exists only inside the window.

**Remark 6.5 (the affirmable/refutable asymmetry).** The two layers have
opposite evidential grain. Record-layer findings are affirmable:
two conflicting signed tip claims are permanent proof of equivocation,
monotone under everything that follows (they are, in fact, claims *about*
prefixes, and fit the record). Liveness is only refutable: no accumulation
of consistent PoPs certifies future honesty. The consuming protocol's
equivocation-detection design states this operationally — "divergence is
permanent; agreement proves nothing forward" — and the trichotomy of the
factoring-trust work gives the general statement: tip currency requires a
liveness holder. This model contributes the impossibility half
(Corollary 6.3): the requirement is not an implementation gap but a
theorem.

**Remark 6.6 (why identity fits and currency does not).** The program of
§5 suffices for a protocol whose load-bearing claims are all monotone
plus one bounded-staleness currency check (a PoP within `δ`). Identity is
such a protocol: key validity at a past position is a prefix property,
and "still valid now" tolerates staleness `δ`. A currency is not: its
central claim — this token is unspent *now*, *everywhere* — is
non-monotone and cross-log at once, the two things the record layer
cannot express. The boundary is thus also a design filter: protocols
whose load-bearing claims are monotone are self-selecting for this
architecture, exactly as non-homomorphic queries were self-selecting out
of `Q_fold`.

### §7. Bounded Partial Sync

**Corollary 7.1 (light client).** A client holding only `(n, R)` that
(i) verifies a consistency proof from its previous root, (ii) verifies
the `k` load-bearing query proofs of Theorem 5.3, and (iii) holds a PoP
within resolution `δ`, has a view that is protocol-honest over the whole
prefix and current-within-`δ`, at cost `O(k log n)` per transition and
storage `O(1)`. Holding leaves is an availability role (serving proofs,
cold audits), not a trust role. ∎

### §8. Cost Summary

`d` abbreviates the dependency count of a class-C entry.

| Operation                         | Cost                   | Premise                   |
| :-------------------------------- | :--------------------- | :------------------------ |
| verify query proof (A, B, D rule) | `O(log n)`             | commitment                |
| extend class-C certificate        | `O(d · log n)`         | checkpoint discipline     |
| boundary proof (adjacent pair)    | `O(log n)`             | ordering invariant proven |
| boundary proof (binary search)    | `O(log² n)`            | commitment                |
| timestamp-lease check             | `O(log n)`             | boundary + window (lease) |
| honest-record proof, incremental  | `O(k log n)`           | prior trusted root        |
| honest-record proof, cold         | `O(n)` once            | genesis                   |
| tip currency                      | not provable (Cor 6.3) | PoP within `δ` instead    |

### Validation

Falsification signposts; each row names what would break the claim.

| Claim                       | Falsified by                                                            |
| :-------------------------- | :---------------------------------------------------------------------- |
| Theorem 2.2 (cost)          | a `Q_fold` query whose dyadic witness exceeds `O(log n)` blocks         |
| Props 2.3/2.4 (subsumption) | an inclusion/consistency verifier not expressible as a `μ = D` fold     |
| Prop 3.4 (localisation)     | a leaf order where first-failure combine is non-associative             |
| Theorem 4.4 (adjacent pair) | a time-ordered log where adjacency fails to pin `β(t)`                  |
| Theorem 5.3 (honesty)       | a class A–D rule whose proof cost is `ω(log n)` under its premise       |
| Theorem 6.2 (monotonicity)  | a query-proof conclusion invalidated by appending leaves                |
| Corollary 6.3 (no currency) | a stable-conclusion proof of tip currency (would refute the trichotomy) |

### Implications

- **Design rule.** Express every load-bearing protocol rule as a fold
  (measure + associative combine) at specification time, and check it
  both directions (the third-homomorphism test). A rule specified as a
  left-to-right *replay check* is already the leftward fold; writing it
  as a fold guarantees the future re-bracketing into a query proof with
  no wire change. Replay and query proof compute the same homomorphism —
  associativity is the entire difference.
- **Layering rule.** Put nothing non-monotone in the record layer, and
  nothing monotone in the liveness layer. The one instrument crossing the
  boundary is the PoP, and it crosses in one direction only: it may be
  archived into the record as history, never promoted into a proof of
  currency.
- **Follow-up.** The consuming protocol should carry its own application
  document mapping each of its normative rules to a class of
  Definition 5.1 and a verifier stance of Definition 5.4 — the
  constraint-by-constraint table is protocol property, not model
  property, and belongs beside the protocol's specs.

### References

- Fold-closed claim log — [companion model](fold-closed-log.md): served
  query class, leases, provable absence, pruning-signal placement,
  complexity floor.
- J. Gibbons, *The Third Homomorphism Theorem*, JFP 1996 — the
  operational test for fold expressibility.
- R. Hinze, R. Paterson, *Finger Trees: A Simple General-Purpose Data
  Structure*, JFP 2006 — search by monotone measure (Construction 4.3c).
- RFC 9162, *Certificate Transparency v2* — inclusion and consistency
  proofs over append-only logs; the proofs subsumed by §2.
- A. Auvolat, F. Taïani, *Merkle Search Trees*, SRDS 2019 — the derived
  keyed tree of class D.
- Cyphr equivocation-detection architecture (Cyphr repository,
  `docs/architecture/equivocation-detection.md`) — the liveness-layer
  design this model's §6 boundary theorem grounds: tip-report exchange,
  the pinned predicate, "divergence is permanent; agreement proves
  nothing forward".
