# MODEL: Temporally-Sparse Merkle Log (TSML)

<!--
  Formal domain model for the Temporally-Sparse Merkle Log data structure.
  Extends the malt verifiable-log model with multi-algorithm support,
  null-fill semantics, and epoch-aware proof generation.

  See: malt docs/models/verifiable-log.md for the base model this extends.
-->

## Domain Classification

**Problem Statement:**

A single RFC 9162 append-only Merkle log supporting dynamic sets of hash
algorithms over a shared topology. Algorithms activate and deactivate
between appends. A new algorithm's view of pre-activation positions
consists of deterministic null constants, enabling O(1) algorithm addition
without retroactive computation while preserving algorithm-independent
verification. Deactivated algorithms freeze at their removal point.

**Domain Characteristics:**

- **State**: Mutable, append-only. Leaf data is immutable once appended.
  The active algorithm set changes between appends.
- **Construction**: Inductive (leaves → internal nodes → root). Classical
  initial algebra.
- **Multi-dimensionality**: Each tree position stores a vector of digests
  indexed by the active algorithm set.
- **Epoch structure**: Algorithm lifetimes partition the leaf space into
  active and inactive regions per algorithm.
- **Proof extraction**: Single-algorithm projection from the multi-algorithm
  tree yields standard RFC 9162 proofs.

## Formalism Selection

| Aspect                  | Detail                                                |
| :---------------------- | :---------------------------------------------------- |
| **Primary Formalism**   | Initial algebra with equational laws                  |
| **Supporting Tools**    | Indexed products over finite algorithm sets           |
| **Decision Matrix Row** | §4 (Algebra) — constructing finite inductive data     |
| **Rationale**           | Direct extension of malt's model; minimal; verifiable |

**Alternatives Considered:**

- **Coalgebra:** State is fully inspectable (no hidden variables). Rejected.
- **Session types:** Proof generation is a pure function. Rejected.
- **Fibrations:** Algorithm-indexed products expressible more simply. Rejected.

## Model

### §1. Carrier Types

```
Alg       — A finite, totally ordered set of hash algorithm identifiers.
Digest    — The type of hash outputs (byte sequences). Fixed-width per Alg.
Bytes     — Arbitrary byte sequences (leaf payloads).
ℕ         — Natural numbers (leaf indices, tree sizes, heights).
AlgSet    — Finite subsets of Alg.
```

### §2. Hash Operations (inherited from malt)

For each algorithm `a ∈ Alg`, the hash operations are:

```
leaf(a, d)    = H_a(0x00 ‖ d)            — Leaf hash
node(a, l, r) = H_a(0x01 ‖ l ‖ r)        — Internal node hash
empty(a)      = H_a("")                   — Empty tree root
```

Domain separation is enforced by the prefix byte (RFC 9162 §2.1):
`leaf(a, d) ≠ node(a, l, r)` for all inputs.

### §3. Null Constants (NEW — extends malt)

**Definition 1** (Null leaf constant). For each algorithm `a`:

```
N₀(a) = H_a(0x02)
```

The byte `0x02` is distinct from `0x00` (leaf prefix) and `0x01` (node
prefix), establishing a third domain through the same single-byte prefix
mechanism used by RFC 9162. No additional payload is necessary — domain
separation is achieved by the prefix byte alone.

**Definition 2** (Null subtree constant). For each algorithm `a` and
height `h ≥ 1`:

```
Nₕ(a) = node(a, Nₕ₋₁(a), Nₕ₋₁(a))
       = H_a(0x01 ‖ Nₕ₋₁(a) ‖ Nₕ₋₁(a))
```

**Observation 1.** `Nₕ(a)` is uniquely determined by `(a, h)`. The null
constant table `{N₀(a), N₁(a), ..., N_H(a)}` is precomputable in `O(H)`
hash operations and requires `O(H)` storage, where `H = ⌈log₂(n)⌉`.

### §4. Algorithm Activation

**Definition 3** (Activation map). An activation map is a partial function:

```
act: Alg ⇀ Vec<(ℕ, ℕ ∪ {∞})>
act(a) = [(start₁, end₁), (start₂, end₂), ...]
```

where each `(startₖ, endₖ)` is an _epoch_ satisfying `startₖ < endₖ`, and
epochs are disjoint and chronologically ordered: `endₖ ≤ startₖ₊₁`. An
algorithm whose final epoch has `endₖ = ∞` is currently active.

**Definition 4** (Active predicate). Algorithm `a` is active at leaf
index `i` iff:

```
active(a, i) ⟺ act(a) is defined ∧ ∃ (startₖ, endₖ) ∈ act(a). startₖ ≤ i < endₖ
```

**Definition 5** (Active set at index). The set of algorithms active at
leaf index `i`:

```
A(i) = { a ∈ dom(act) | active(a, i) }
```

### §5. TSML State

**Definition 6** (TSML state). A TSML state is a tuple:

```
S = (leaves, size, act, stacks)
```

where:

- `leaves: Vec<Bytes>` — raw leaf payloads (shared across all algorithms)
- `size: ℕ` — number of appended leaves (`= |leaves|`)
- `act: Alg ⇀ Vec<(ℕ, ℕ ∪ {∞})>` — algorithm activation map (epoch vectors)
- `stacks: Alg → Vec<Digest>` — per-algorithm frontier stacks

For each `a ∈ active_algs(S)` (algorithms whose final epoch has `end = ∞`),
`stacks(a)` is the frontier stack for algorithm `a` over the global tree.

### §6. Leaf Value Function

**Definition 7** (Leaf value). The digest stored at tree position `i` for
algorithm `a`:

```
V(a, i) = leaf(a, leaves[i])    if active(a, i)
         = N₀(a)                 otherwise
```

This is the central definition. Null constants occupy positions outside an
algorithm's active window. No retroactive computation is needed because the
null values are deterministic.

### §7. Append Operation

**Definition 8** (Append). Given state `S` and payload `d`:

```
append(S, d) → S' where:
  S'.leaves = S.leaves ++ [d]
  S'.size   = S.size + 1
  S'.act    = S.act
  for each a ∈ active_algs(S):
    let h = V(a, S.size)                    — real hash or null constant
    let merge_count = cto(S.size)           — count trailing ones
    S'.stacks(a) = push(h, S.stacks(a))
    for _ in 0..merge_count:
      let r = pop(S'.stacks(a))
      let l = pop(S'.stacks(a))
      push(node(a, l, r), S'.stacks(a))
```

where `cto(n)` counts trailing one-bits in the binary representation of `n`.

**Note:** Frozen algorithms (whose final epoch end ≤ `S.size`) are NOT
updated. Their frontier stacks are immutable until resumed.

### §8. Algorithm Addition

**Definition 9** (Add algorithm). Given state `S`, new algorithm `a`, at
the current tree size:

```
add_alg(S, a) → S' where:
  S'.act    = S.act ∪ {a ↦ [(S.size, ∞)]}
  S'.stacks(a) = null_prefix_peaks(a, S.size)
  — all other fields unchanged
```

**Definition 10** (Null prefix peaks). The frontier stack for algorithm `a`
over a tree of `K` null leaves:

```
null_prefix_peaks(a, K) = [Nₕᵢ(a) | for each bit i set in K,
                                      in strictly descending order of i]
```

where `hᵢ` is the bit position. Descending order ensures the largest
subtrees sit at the bottom of the stack, aligning with the `push`/`pop`
semantics of Definition 8. For example, `K = 6` (binary `110`) yields
stack `[N₂(a), N₁(a)]` with `N₁(a)` on top, ready for the next merge.

This follows from the fact that a subtree of `2^h` identical null leaves
has root `Nₕ(a)`, and the frontier stack decomposes `K` into its binary
components (MMR peaks).

**Complexity:** `O(⌈log₂(K)⌉)` hash operations (computing the null constant
table). Zero retroactive computation over historical leaf data.

### §9. Algorithm Removal

**Definition 11** (Remove algorithm). Given state `S`, algorithm `a` to
remove:

```
remove_alg(S, a) → S' where:
  Let act(a) = [..., (startₖ, ∞)]      — last epoch must be open
  S'.act(a) = [..., (startₖ, S.size)]   — close last epoch
  S'.stacks(a) is frozen (no further updates until resumed)
  — all other fields unchanged
```

The removed algorithm's root at `S.size` is its final root. Future appends
do not update its frontier stack.

**Resolved:** Removed algorithms freeze. Null-filling a deactivated algorithm
implies unbounded maintenance cost (computing `Nₕ(a)` merges for every
subsequent append, indefinitely) for an algorithm no longer in use.
Freezing aligns the data structure's topology with its cryptographic
authority: the manifest records `tree_size(a) = last(act(a)).end`,
and any proof request beyond that boundary is structurally out-of-bounds.

### §9b. Algorithm Resumption

**Definition 11b** (Resume algorithm). Given state `S`, frozen algorithm
`a` to reactivate:

```
resume_alg(S, a) → S' where:
  Let act(a) = [..., (startₖ, endₖ)]    — last epoch must be closed (endₖ ≠ ∞)
  Let gap = S.size - endₖ               — null positions since deactivation
  S'.stacks(a) = merge_stacks(S.stacks(a), null_prefix_peaks(a, gap),
                               hasher_a, endₖ, gap)
  S'.act(a) = act(a) ++ [(S.size, ∞)]   — append new open epoch
  — all other fields unchanged
```

**Definition 11c** (Frontier merge). `merge_stacks(frozen, gap, hasher, D, G)`
performs binary addition of two frontier stacks representing `D` and `G`
leaves respectively, producing the correct frontier for `D + G` leaves:

```
merge_stacks(frozen, gap, hasher, D, G):
  for bit in 0..max_bits(D + G):
    f_peak = frozen peak at this bit level (if D has bit set)
    g_peak = gap peak at this bit level (if G has bit set)
    c_peak = carry from previous level (if any)

    Tree ordering: f_peak < c_peak < g_peak

    match count(f_peak, g_peak, c_peak):
      1 → keep at this level
      2 → merge(left, right) → carry
      3 → keep rightmost, merge(left, middle) → carry
```

The frozen stack covers positions `[0, D)`, the gap covers `[D, D+G)`.
At every bit level, tree ordering is enforced: frozen peaks are leftmost,
carry (from lower-level merges) is middle, gap peaks are rightmost.

**Complexity:** `O(log(D + G))` hash operations.

### §10. Root Extraction

**Definition 12** (Per-algorithm root). For algorithm `a` with frontier
stack `stacks(a)`:

```
root(a) = empty(a)                                         if stacks(a) = []
        = fold_right(λ(acc, left). node(a, left, acc),
                     stacks(a))                            otherwise
```

This is identical to malt's root extraction, applied per algorithm.

**Definition 13** (TSML Manifest). The state manifest is a structured snapshot:

```
Manifest = {
  global_tree_size: S.size,
  algorithms: {
    a ↦ {
      root:               root(a),
      activation_index:   first(act(a)).start,     — first epoch start
      deactivation_index: last(act(a)).end,         — ∞ if active
      tree_size:          tree_size(a),
      epochs:             [(startₖ, endₖ) | ...]    — full epoch history
    }
    | a ∈ dom(act)
  }
}
```

where `tree_size(a) = last(act(a)).end` if deactivated, else
`global_tree_size`.

### §11. Projection

**Definition 14** (Single-algorithm projection). The projection of a TSML
onto algorithm `a` yields a sequence of digests:

```
project(S, a) = [V(a, i) | 0 ≤ i < tree_size(a)]
```

This sequence is equivalent to the leaves of a standard malt::Log where
positions outside `a`'s active window contain `N₀(a)` and positions
inside contain `leaf(a, leaves[i])`.

**Theorem 1** (Projection equivalence). For any algorithm `a`, the root
computed by `root(a)` from the TSML frontier stack equals the root of a
batch-constructed malt::Log over the projected leaf sequence:

```
root(a) = malt::mth(hasher_a, project(S, a))
```

### §12. Proof Generation

**Definition 15** (Inclusion proof). For algorithm `a` and leaf index
`index`:

```
inclusion_proof(S, a, index) =
  malt::gen_path(hasher_a, index, project(S, a))
```

The proof path contains digests from algorithm `a` only. Some siblings
may be null subtree constants (for branches in the null prefix), but
the verifier processes them identically to any other digest.

**Definition 16** (Consistency proof). For algorithm `a` and old tree
size `old_size`:

```
consistency_proof(S, a, old_size) =
  malt::gen_subproof(hasher_a, old_size, project(S, a), true)
```

### §13. Equational Laws

The following laws extend malt's invariants to the multi-algorithm setting.

#### A-EQUIV-TSML — Incremental equals batch

For all algorithms in the activation map, the incrementally maintained
root equals the batch-computed root over the projected leaf sequence:

```
∀ a ∈ dom(act).
  root(a) = malt::mth(hasher_a, project(S, a))
```

For active algorithms, this follows from malt's A-EQUIV applied at each
append. For frozen algorithms, `stacks(a)` ceased updating at the last epoch's close
and `project(S, a)` is bounded at `tree_size(a) = last(act(a)).end` — the
frozen stack and the truncated projection agree by construction. For resumed
algorithms, `merge_stacks` (Definition 11c) fast-forwards the stack through
the null gap, preserving the invariant. This is Theorem 1, restated as a
universal invariant.

#### A-STACK-TSML — Frontier stack size invariant

For all algorithms in the activation map:

```
∀ a ∈ dom(act).
  |stacks(a)| = popcount(tree_size(a))
```

For active algorithms, `tree_size(a) = global_tree_size`. For frozen
algorithms, `tree_size(a) = last(act(a)).end`. Resume (Definition 11b)
preserves this invariant via `merge_stacks`. This single law governs
the entire state map.

#### N-DET — Null determinism

```
∀ a, h.  Nₕ(a) is uniquely determined by (a, h).
```

Null subtrees are stateless — they require no storage and are computable
from first principles.

#### D-SEP — Domain separation

```
∀ a, d.       N₀(a) ≠ leaf(a, d)        — null ≠ real leaf  (0x02 ≠ 0x00)
∀ a, l, r.    N₀(a) ≠ node(a, l, r)     — null ≠ interior   (0x02 ≠ 0x01)
∀ a, d, l, r. leaf(a, d) ≠ node(a, l, r) — leaf ≠ interior   (0x00 ≠ 0x01)
```

Three-way domain separation across all tree domains.

#### I-SOUND-TSML — Inclusion proof soundness

For all active `(a, i)` where `active(a, i)`:

```
let proof = inclusion_proof(S, a, i)
let leaf_hash = leaf(a, leaves[i])
⟹  verify_inclusion(hasher_a, leaf_hash, proof, root(a)) = true
```

#### K-SOUND-TSML — Consistency proof soundness

For all `a` and `old_size < tree_size(a)`:

```
let proof = consistency_proof(S, a, old_size)
let old_root = root_at(a, old_size)
⟹  verify_consistency(hasher_a, proof, old_root, root(a)) = true
```

#### T-BOUND — Temporal binding

For all `a` and `i` in any inactive gap (outside all epochs):

```
∀ a, i where ¬active(a, i) ∧ i < tree_size(a):
  ∄ d ∈ Bytes.
    verify_inclusion(hasher_a, leaf(a, d), inclusion_proof(S, a, i), root(a)) = true
```

No payload can produce a valid inclusion proof at an inactive position,
because the tree contains `N₀(a)` at that position, and `leaf(a, d) ≠ N₀(a)`
by D-SEP. This covers the null prefix (before first activation), the null
suffix (after final deactivation for frozen algorithms, bounded by
`tree_size(a)`), and any inter-epoch gaps introduced by resumption.

#### ALG-IND — Algorithm independence

Under the Random Oracle Model:

```
∀ a ≠ b.  project(S, a) and project(S, b) are mutually incompressible.
```

Knowing one algorithm's digest tree reveals zero information about any
other algorithm's digest tree.

#### PROJ-VALID — Projection produces valid malt tree

```
∀ a ∈ dom(act).
  project(S, a) is a valid malt::Log leaf sequence.
  All malt invariants (A-EQUIV, A-STACK, I-SOUND, K-SOUND) hold
  for the projected tree.
```

This is the composition law: TSML correctness reduces to malt correctness
per algorithm, plus the multi-algorithm extension laws above.

## Validation

| Check                    | Result | Detail                                                                                                                                                                                              |
| :----------------------- | :----- | :-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| A-EQUIV-TSML             | PASS   | Follows from malt's A-EQUIV applied per-algorithm over the projected sequence. The null constants are just another leaf value.                                                                      |
| A-STACK-TSML             | PASS   | Active algorithms track `popcount(global_tree_size)`, frozen algorithms track `popcount(last(act(a)).end)`. Resume via `merge_stacks` preserves the invariant. Unified by `popcount(tree_size(a))`. |
| N-DET                    | PASS   | By construction: `Nₕ(a)` is a pure function of `(a, h)`.                                                                                                                                            |
| D-SEP                    | PASS   | Three distinct prefix bytes (0x00, 0x01, 0x02) under cryptographic hash. Collision requires breaking preimage resistance.                                                                           |
| I-SOUND-TSML             | PASS   | Reduces to malt's I-SOUND over the projected leaf sequence. Null leaves verify as `N₀(a)`, not as real data.                                                                                        |
| K-SOUND-TSML             | PASS   | Reduces to malt's K-SOUND. Null subtrees are valid tree nodes.                                                                                                                                      |
| T-BOUND                  | PASS   | All inactive positions (pre-activation, inter-epoch gaps, post-deactivation): D-SEP prevents forgery. Beyond `tree_size(a)`: projection bounds prevent proof generation.                            |
| ALG-IND                  | PASS   | Follows from ROM: distinct hash functions produce mutually incompressible outputs.                                                                                                                  |
| PROJ-VALID               | PASS   | By construction: each algorithm's projected sequence is a valid input to malt's batch construction.                                                                                                 |
| **Internal consistency** | PASS   | No equational law contradicts another. The laws are layered: D-SEP → T-BOUND, A-EQUIV-TSML → PROJ-VALID, ALG-IND standalone.                                                                        |
| **External adequacy**    | PASS   | The model captures all design constraints from the original exploration.                                                                                                                            |
| **Minimality**           | PASS   | No formalism beyond initial algebra + indexed products is used.                                                                                                                                     |

### Performance Bounds

| Operation                   | Complexity            | Notes                               |
| :-------------------------- | :-------------------- | :---------------------------------- |
| Append (per algorithm)      | O(1) amortized        | Same as malt                        |
| Append (total)              | O(\|A(i)\|) amortized | Linear in active algorithm count    |
| Algorithm addition          | O(log K)              | Null prefix peak computation        |
| Algorithm removal           | O(1)                  | Freeze frontier stack               |
| Algorithm resumption        | O(log n)              | Null gap peaks + binary merge       |
| Root extraction (per alg)   | O(log n)              | Frontier stack fold                 |
| Inclusion proof (per alg)   | O(log n)              | Global tree depth                   |
| Consistency proof (per alg) | O(log n)              | Global tree depth                   |
| Null constant table         | O(log n) precompute   | Per algorithm, once                 |
| Total storage               | Σ O(nᵢ)               | Where nᵢ = active duration of alg i |

### Proof Size Trade-off (Resolved: Elided Proofs)

In independent MALTs, algorithm `a` active for `nₐ` appends has proof depth
`O(log nₐ)`. In TSML, proof depth is `O(log n)` where `n` is global tree
size. If `nₐ ≪ n`, TSML proofs are deeper.

**Resolution — Elided proofs.** Null subtree siblings are deterministic and
need not be transmitted. The proof flow is:

1. **Server (prover):** Generates the full `malt` proof. Siblings whose
   entire leaf-coverage range falls outside all active epochs are null
   subtrees. The server omits them from the wire payload.
2. **TSML client envelope:** The client knows `tree_size`, `index`, and
   the epoch list. It walks the virtual tree path, detects positions fully
   inside an inactive gap, synthesizes `Nₕ(a)` locally, and injects them
   into the proof array.
3. **Core verifier:** The envelope hands the rehydrated, full proof to the
   unmodified `malt::verify_*` function.

Wire proof size collapses to `O(log nₐ)`, neutralizing TSML's only
theoretical overhead while preserving verifier independence.

## Implications

### Implementation Guidance

1. **New crate, not malt modification.** TSML extends malt's model but
   changes the fundamental abstraction from single-algorithm to multi-algorithm.
   The `TreeHasher` trait doesn't accommodate multi-algorithm operations.
   Create a `tsml` crate that depends on `malt` for proof primitives
   (`gen_path`, `gen_subproof`, `verify_inclusion`, `verify_consistency`).

2. **Core data structure.** The TSML state maps directly to:

   ```rust
   struct Log {
       storage: S,                                  // raw payloads via Storage trait
       algs: BTreeMap<Alg, AlgState>,                // per-algorithm state
   }

   struct AlgState {
       epochs: Vec<(u64, u64)>,                      // disjoint epoch intervals
       stack: Vec<Vec<u8>>,                           // frontier stack
       hasher: Box<dyn Hasher>,                       // hash implementation
       null_table: NullTable,                         // precomputed Nₕ(a)
   }
   ```

3. **Manifest.** Introduce a structured manifest type that includes
   `global_tree_size`, per-algorithm roots, and activation metadata.

### Testing Strategy

- **A-EQUIV-TSML:** For each algorithm, verify incremental root equals batch.
- **T-BOUND:** Attempt inclusion proof at null position with arbitrary data;
  verify it fails.
- **Cross-algorithm independence:** Verify that changing data in one algorithm's
  active range doesn't affect another algorithm's root.
- **Algorithm addition:** Add algorithm mid-stream, verify null prefix peaks
  are correct by comparing against batch construction.
- **Parity:** TSML proofs must verify against standard `malt::verify_*`
  functions — the verifier is unmodified.

### Architecture Decisions

- **Algorithm removal: freeze.** Deactivated algorithms freeze at their
  removal point. Zero ongoing maintenance cost. The manifest records
  the terminal `tree_size(a)` explicitly.

- **Proof transmission: elide null siblings.** The TSML client envelope
  rehydrates deterministic null subtree siblings before handing to the
  standard `malt` verifier. Wire size is `O(log nₐ)`, not `O(log n)`.

- **Manifest wire format.** The manifest's serialization format is a
  consumer concern (candidate: deterministic canonical serialization
  keyed by algorithm IDs).

### Remaining Open Questions

1. Manifest wire format (JSON vs. CBOR vs. other canonical form)

**Resolved:** Elided proof wire encoding requires no explicit metadata.
The client deterministically identifies omitted siblings via interval
arithmetic: for each sibling in the proof path, the client computes its
leaf-coverage range `[start, end)`. If the range overlaps no active epoch,
the entire subtree is null and was elided — the client synthesizes `Nₕ(a)`
locally. Otherwise, the sibling was transmitted. Both parties share
`tree_size(a)`, `index`, and the epoch list, ensuring lockstep
agreement with zero wire overhead.
