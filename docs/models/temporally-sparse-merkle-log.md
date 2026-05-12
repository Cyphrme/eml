# MODEL: Temporally-Sparse Merkle Log (TSML)

<!--
  Formal domain model for the Temporally-Sparse Merkle Log data structure.
  Extends the malt verifiable-log model with multi-algorithm support,
  null-fill semantics, and epoch-aware proof generation.

  See: .sketches/2026-05-12-topology-invariant-malt.md for exploration history.
  See: malt docs/models/verifiable-log.md for the base model this extends.
-->

## Domain Classification

**Problem Statement:**

A single RFC 9162 append-only Merkle log supporting dynamic sets of hash
algorithms over a shared topology. Algorithms activate and deactivate at
commit boundaries. Pre-activation positions are filled with deterministic
null constants, enabling O(1) algorithm addition without retroactive
computation while preserving algorithm-independent verification. Deactivated
algorithms freeze at their removal point.

**Domain Characteristics:**

- **State**: Mutable, append-only. Leaf data is immutable once committed.
  The active algorithm set changes at commit boundaries.
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
act: Alg ⇀ (ℕ, ℕ ∪ {∞})
act(a) = (activation_commit, deactivation_commit)
```

where `activation_commit < deactivation_commit`. Algorithms with
`deactivation_commit = ∞` are currently active.

**Definition 4** (Active predicate). Algorithm `a` is active at leaf
index `i` iff:

```
active(a, i) ⟺ act(a) is defined ∧ act(a).activation ≤ i < act(a).deactivation
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
- `act: Alg ⇀ (ℕ, ℕ ∪ {∞})` — algorithm activation map
- `stacks: Alg → Vec<Digest>` — per-algorithm frontier stacks

For each `a ∈ active_algs(S)` (algorithms where `act(a).deactivation = ∞`),
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

**Note:** Frozen algorithms (where `act(a).deactivation ≤ S.size`) are NOT
updated. Their frontier stacks are immutable after deactivation.

### §8. Algorithm Addition

**Definition 9** (Add algorithm). Given state `S`, new algorithm `a`, at
the current tree size:

```
add_alg(S, a) → S' where:
  S'.act    = S.act ∪ {a ↦ (S.size, ∞)}
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
  S'.act(a) = (S.act(a).activation, S.size)     — set deactivation
  S'.stacks(a) is frozen (no further updates)
  — all other fields unchanged
```

The removed algorithm's root at `S.size` is its final root. Future appends
do not update its frontier stack.

**Resolved:** Removed algorithms freeze. Null-filling a deactivated algorithm
implies unbounded maintenance cost (computing `Nₕ(a)` merges for every
subsequent commit, indefinitely) for an algorithm the identity no longer
trusts. Freezing aligns the data structure's topology with its cryptographic
authority: the CR Manifest records `tree_size(a) = act(a).deactivation`,
and any proof request beyond that boundary is structurally out-of-bounds.

### §10. Root Extraction

**Definition 12** (Per-algorithm root). For algorithm `a` with frontier
stack `stacks(a)`:

```
root(a) = empty(a)                                         if stacks(a) = []
        = fold_right(λ(acc, left). node(a, left, acc),
                     stacks(a))                            otherwise
```

This is identical to malt's root extraction, applied per algorithm.

**Definition 13** (CR Manifest). The Commit Root is a structured manifest:

```
CR = {
  global_tree_size: S.size,
  algorithms: {
    a ↦ {
      root:               root(a),
      activation_commit:  act(a).activation,
      deactivation_commit: act(a).deactivation,    — ∞ if active
      tree_size:          tree_size(a)
    }
    | a ∈ dom(act)
  }
}
```

where `tree_size(a) = act(a).deactivation` if deactivated, else
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
append. For frozen algorithms, `stacks(a)` ceased updating at
`act(a).deactivation` and `project(S, a)` is bounded at `tree_size(a) =
act(a).deactivation` — the frozen stack and the truncated projection
agree by construction. This is Theorem 1, restated as a universal invariant.

#### A-STACK-TSML — Frontier stack size invariant

For all algorithms in the activation map:

```
∀ a ∈ dom(act).
  |stacks(a)| = popcount(tree_size(a))
```

For active algorithms, `tree_size(a) = global_tree_size`. For frozen
algorithms, `tree_size(a) = act(a).deactivation`. This single law
governs the entire state map.

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

For all `a` and `i` in the null prefix (before activation):

```
∀ a, i where i < act(a).activation:
  ∄ d ∈ Bytes.
    verify_inclusion(hasher_a, leaf(a, d), inclusion_proof(S, a, i), root(a)) = true
```

No payload can produce a valid inclusion proof at a null-prefix position,
because the tree contains `N₀(a)` at that position, and `leaf(a, d) ≠ N₀(a)`
by D-SEP. For post-deactivation indices (`i ≥ act(a).deactivation`), the
projection is structurally bounded at `tree_size(a)` — the proof request
fails domain bounds before cryptography applies.

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

| Check                    | Result | Detail                                                                                                                                              |
| :----------------------- | :----- | :-------------------------------------------------------------------------------------------------------------------------------------------------- |
| A-EQUIV-TSML             | PASS   | Follows from malt's A-EQUIV applied per-algorithm over the projected sequence. The null constants are just another leaf value.                      |
| A-STACK-TSML             | PASS   | Active algorithms track `popcount(global_tree_size)`, frozen algorithms track `popcount(deactivation_commit)`. Unified by `popcount(tree_size(a))`. |
| N-DET                    | PASS   | By construction: `Nₕ(a)` is a pure function of `(a, h)`.                                                                                            |
| D-SEP                    | PASS   | Three distinct prefix bytes (0x00, 0x01, 0x02) under cryptographic hash. Collision requires breaking preimage resistance.                           |
| I-SOUND-TSML             | PASS   | Reduces to malt's I-SOUND over the projected leaf sequence. Null leaves verify as `N₀(a)`, not as real data.                                        |
| K-SOUND-TSML             | PASS   | Reduces to malt's K-SOUND. Null subtrees are valid tree nodes.                                                                                      |
| T-BOUND                  | PASS   | Pre-activation: D-SEP prevents forgery. Post-deactivation: projection bounds prevent proof generation.                                              |
| ALG-IND                  | PASS   | Follows from ROM: distinct hash functions produce mutually incompressible outputs.                                                                  |
| PROJ-VALID               | PASS   | By construction: each algorithm's projected sequence is a valid input to malt's batch construction.                                                 |
| **Internal consistency** | PASS   | No equational law contradicts another. The laws are layered: D-SEP → T-BOUND, A-EQUIV-TSML → PROJ-VALID, ALG-IND standalone.                        |
| **External adequacy**    | PASS   | The model captures all seven design constraints (C1–C7) from the sketch.                                                                            |
| **Minimality**           | PASS   | No formalism beyond initial algebra + indexed products is used.                                                                                     |

### Performance Bounds

| Operation                   | Complexity            | Notes                               |
| :-------------------------- | :-------------------- | :---------------------------------- |
| Append (per algorithm)      | O(1) amortized        | Same as malt                        |
| Append (total)              | O(\|A(i)\|) amortized | Linear in active algorithm count    |
| Algorithm addition          | O(log K)              | Null prefix peak computation        |
| Algorithm removal           | O(1)                  | Freeze frontier stack               |
| Root extraction (per alg)   | O(log n)              | Frontier stack fold                 |
| Inclusion proof (per alg)   | O(log n)              | Global tree depth                   |
| Consistency proof (per alg) | O(log n)              | Global tree depth                   |
| Null constant table         | O(log n) precompute   | Per algorithm, once                 |
| Total storage               | Σ O(nᵢ)               | Where nᵢ = active duration of alg i |

### Proof Size Trade-off (Resolved: Elided Proofs)

In independent MALTs, algorithm `a` active for `nₐ` commits has proof depth
`O(log nₐ)`. In TSML, proof depth is `O(log n)` where `n` is global tree
size. If `nₐ ≪ n`, TSML proofs are deeper.

**Resolution — Elided proofs.** Null subtree siblings are deterministic and
need not be transmitted. The proof flow is:

1. **Server (prover):** Generates the full `malt` proof. Siblings whose
   entire leaf-coverage range falls strictly below `activation_commit` are
   null subtrees. The server omits them from the wire payload.
2. **TSML client envelope:** The client knows `tree_size`, `index`, and
   `activation_commit`. It walks the virtual tree path, detects positions
   fully inside the inactive epoch, synthesizes `Nₕ(a)` locally, and
   injects them into the proof array.
3. **Core verifier (C6 preserved):** The envelope hands the rehydrated,
   full proof to the unmodified `malt::verify_*` function.

Wire proof size collapses to `O(log nₐ)`, neutralizing TSML's only
theoretical overhead while preserving verifier independence (C6).

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
       leaves: Vec<Vec<u8>>,           // raw payloads
       act: BTreeMap<Alg, (u64, u64)>, // activation map
       stacks: BTreeMap<Alg, Vec<Vec<u8>>>, // per-alg frontier stacks
       null_tables: BTreeMap<Alg, Vec<Vec<u8>>>, // precomputed Nₕ(a)
   }
   ```

3. **CR Manifest.** Introduce a structured `CommitRoot` type that includes
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
  removal point. Zero ongoing maintenance cost. The CR Manifest records
  the terminal `tree_size(a)` explicitly.

- **Proof transmission: elide null siblings.** The TSML client envelope
  rehydrates deterministic null subtree siblings before handing to the
  standard `malt` verifier. Wire size is `O(log nₐ)`, not `O(log n)`.

- **CR format.** The CR Manifest replaces the current `MultihashDigest` for
  the commit root. Wire format is a specification concern (candidate:
  deterministic canonical serialization keyed by algorithm IDs). This is a
  SPEC-level change that requires careful migration planning.

### Remaining Open Questions

1. CR Manifest wire format (Coz-native JSON vs. CBOR vs. other canonical form)

**Resolved:** Elided proof wire encoding requires no explicit metadata.
The client deterministically identifies omitted siblings via interval
arithmetic: for each sibling in the proof path, the client computes its
leaf-coverage range `[start, end)`. If `end ≤ activation_commit`, the
entire subtree is null and was elided — the client synthesizes `Nₕ(a)`
locally. Otherwise, the sibling was transmitted. Both parties share
`tree_size(a)`, `index`, and `activation_commit`, ensuring lockstep
agreement with zero wire overhead.
