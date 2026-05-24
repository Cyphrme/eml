# MODEL: Epoch Merkle Log (EML)

<!--
  Formal domain model for the Epoch Merkle Log data structure.
  Defines EML multi-algorithm support, null-fill semantics, and
  epoch-aware proof generation.
-->

## Domain Classification

**Problem Statement:**

A single RFC 9162 append-only Merkle log supporting dynamic sets of hash
algorithms over a shared topology. Algorithms activate and deactivate
between appends. A new algorithm's view of pre-activation positions
consists of deterministic null constants, enabling O(log n) algorithm addition
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
| **Primary Formalism**   | Free magma and algebra homomorphisms                  |
| **Supporting Tools**    | Indexed products over finite algorithm sets           |
| **Decision Matrix Row** | §4 (Algebra) — constructing finite inductive data     |
| **Rationale**           | Structural-to-homomorphic decoupling; minimal; verified|

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

### §2. Hash Operations

For each algorithm `a ∈ Alg`, the hash operations are:

```
leaf(a, d)    = H_a(0x00 ‖ d)            — Leaf hash
node(a, l, r) = H_a(0x01 ‖ l ‖ r)        — Internal node hash
empty(a)      = H_a("")                   — Empty tree root
```

Domain separation is enforced by the prefix byte (RFC 9162 §2.1):
`leaf(a, d) ≠ node(a, l, r)` for all inputs.

### §3. Null Constants (NEW)

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

### §5. EML State

**Definition 6** (EML state). An EML state is a tuple:

```
S = (leaves, size, act, stacks, nodes)
```

where:

- `leaves: Vec<Bytes>` — raw leaf payloads (shared across all algorithms)
- `size: ℕ` — number of appended leaves (`= |leaves|`)
- `act: Alg ⇀ Vec<(ℕ, ℕ ∪ {∞})>` — algorithm activation map (epoch vectors)
- `stacks: Alg → Vec<Digest>` — per-algorithm frontier stacks
- `nodes: Alg ⇀ ((ℕ, ℕ) ⇀ Digest)` — per-algorithm sealed internal node hashes

For each `a ∈ active_algs(S)` (algorithms whose final epoch has `end = ∞`),
`stacks(a)` is the frontier stack for algorithm `a` over the global tree.

The `nodes` store maps `(a, left, height)` to the sealed root hash of the
subtree covering leaves `[left, left + 2^height)`. Entries are persisted
during the CTO merge in `append` (Definition 8). This store enables
O(log n) proof generation (§12) without materializing the full projection.

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
    let left_pos = S.size                   — position of this leaf
    let height = 0
    S'.stacks(a) = push(h, S.stacks(a))
    for _ in 0..merge_count:
      let r = pop(S'.stacks(a))
      let l = pop(S'.stacks(a))
      let parent = node(a, l, r)
      left_pos = left_pos - 2^height       — left edge of merged subtree
      height = height + 1
      S'.nodes(a)[(left_pos, height)] = parent   — persist sealed node
      push(parent, S'.stacks(a))
```

where `cto(n)` counts trailing one-bits in the binary representation of `n`.

The node persistence adds `O(1)` amortized storage writes per algorithm
per append — zero additional hash computations beyond what the CTO merge
already performs.

**Note:** Frozen algorithms (whose final epoch end ≤ `S.size`) are NOT
updated. Their frontier stacks and node stores are immutable until resumed.

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

**Observation 2** (Null subtree storage optimization). The peaks produced by
`null_prefix_peaks` are `Nₕ(a)` values — deterministic from `(a, h)` alone.
These need not be persisted in `nodes(a)` because `subtree_root` (Definition
14c) reconstructs them via the null constant table in O(1). Only nodes whose
subtrees contain at least one active leaf require storage.

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

**Definition 11c** (Frontier extension). `extend_with_nulls(frozen, hasher, D, G)`
appends `G` null leaves to a frozen frontier stack of `D` leaves, producing
the correct frontier for `D + G` leaves:

```
extend_with_nulls(frozen, hasher, nodes_a, D, G):
  stack ← copy(frozen)
  for i in 0..G:
    n ← D + i                  // tree size before this append
    left_pos ← n               // position of this null leaf
    height ← 0
    stack.push(null(hasher))    // append N₀
    for _ in 0..cto(n):         // standard frontier merge
      right ← stack.pop()
      left  ← stack.pop()
      parent ← node(hasher, left, right)
      left_pos ← left_pos - 2^height
      height ← height + 1
      nodes_a[(left_pos, height)] ← parent   // persist sealed node
      stack.push(parent)
  return stack
```

This is the standard CTO-based frontier append algorithm (Definition 8)
applied with null leaf constants. The frozen stack covers positions
`[0, D)`, and positions `[D, D+G)` are filled with null constants.

Node persistence during gap fill follows the same rule as Definition 8.
Merges that combine a pre-existing active subtree with null gap leaves
produce **mixed** nodes that cannot be derived from the null constant
table alone — these must be persisted. By Observation 2, purely-null
subtrees within the gap are reconstructible from NullTable and need
not be stored; implementations may elide them.

**Complexity:** `O(G)` hash operations and `O(G)` node stores (amortized
`O(1)` per append).

### §10. Root Extraction

**Definition 12** (Per-algorithm root). For algorithm `a` with frontier
stack `stacks(a)`:

```
root(a) = empty(a)                                         if stacks(a) = []
        = fold_right(λ(acc, left). node(a, left, acc),
                     stacks(a))                            otherwise
```

This is identical to standard RFC 9162 root extraction, applied per algorithm.

**Definition 13** (EML Manifest). The state manifest is a structured snapshot:

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

**Definition 13b** (Signed Tree Head). The EML's externally published
commitment is:

```
STH = Sign_σ(
  n,
  t,
  { (a, root(a), tree_size(a), H_a(act(a))) | a ∈ dom(act) }
)
```

where `n` is the global tree size, `t` is a timestamp, `σ` is the log's
signing key, and `H_a(act(a))` is a cryptographic digest of a canonical,
deterministic serialization of algorithm `a`'s activation map (epochs,
Definition 3) using its own hash function `H_a`.
The serialization format is deterministic and injective: distinct logical
activation maps produce distinct byte sequences. The concrete serialization
format is big-endian binary encoding (Definition 13c).

The per-algorithm entries include `tree_size(a)` and `H_a(act(a))` alongside
`root(a)`. Although `tree_size(a)` is derivable from `act` (it equals `n` for
active algorithms and `e_k` for frozen ones), its inclusion in the
signed tuple enables epoch-unaware clients to verify standard RFC 9162
proofs using only the STH, without possessing or parsing the activation
map.

**Definition 13c** (Canonical Activation Map Serialization). The canonical
serialization of an algorithm `a`'s epochs `act(a) = [(s₁, e₁), (s₂, e₂), ...]`
is defined as:
- `|act(a)|` represented as a 64-bit big-endian integer.
- For each epoch `(s_k, e_k)`:
  - `s_k` represented as a 64-bit big-endian integer.
  - `e_k` represented as a 64-bit big-endian integer (with `u64::MAX` for active).
  - The hash function `H_a` hashes this serialization directly without any domain prefix.

### §11. Projection (Specification Oracle)

**Definition 14** (Single-algorithm projection). The projection of an EML
onto algorithm `a` yields a sequence of digests:

```
project(S, a) = [V(a, i) | 0 ≤ i < tree_size(a)]
```

This sequence is equivalent to the leaves of a standard single-algorithm Merkle tree where
positions outside `a`'s active window contain `N₀(a)` and positions
inside contain `leaf(a, leaves[i])`.

**Oracle designation.** `project` is a specification oracle — an `O(n)`
mathematical construction used exclusively by the theorems (§13)
to prove correctness. It is not used operationally. Proof generation
uses `subtree_root` (Definition 14c), which achieves `O(log n)` by
querying the `nodes` store directly.

**Theorem 2** (Projection equivalence). For any algorithm `a`, the root
computed by `root(a)` from the EML frontier stack equals the root of a
batch-constructed Merkle tree over the projected leaf sequence:

```
root(a) = mthDigest(project(S, a))
```

### §11b. Active Range Predicate

**Definition 14b** (Active range). Algorithm `a` has active content in the
half-open range `[lo, hi)` iff any epoch overlaps it:

```
active_range(a, lo, hi) ⟺ ∃ (startₖ, endₖ) ∈ act(a). startₖ < hi ∧ endₖ > lo
```

This generalizes `active(a, i)` (Definition 4) from a single index to an
interval. It is `O(k)` where `k = |act(a)|` (the number of epochs).

### §11c. Subtree Root Query

**Definition 14c** (Subtree root). The root hash of the subtree covering
leaves `[lo, hi)` for algorithm `a`:

```
subtree_root(S, a, lo, hi) =
  empty(a)                                       if hi - lo = 0
  V(a, lo)                                       if hi - lo = 1
  Nₕ(a) where h = log₂(hi - lo)                 if ¬active_range(a, lo, hi)
                                                     ∧ hi - lo is a power of 2
  null_range_root(a, hi - lo)                    if ¬active_range(a, lo, hi)
  nodes(a)[(lo, log₂(hi - lo))]                  if hi - lo is a power of 2
                                                     ∧ (lo, log₂(hi - lo)) ∈ nodes(a)
  node(a,                                        otherwise (RFC 9162 split)
    subtree_root(S, a, lo, lo + k),
    subtree_root(S, a, lo + k, hi))
  where k = largest_pow2_lt(hi - lo)
```

**Definition 14d** (Null range root). The root of `size` consecutive null
leaves for algorithm `a`:

```
null_range_root(a, size) =
  N₀(a)                                         if size = 1
  node(a,                                        if size > 1
    Nₖ(a),
    null_range_root(a, size - 2^k))
  where k = ⌊log₂(size)⌋
```

This decomposes a non-power-of-2 null range into power-of-2 subtrees
whose roots are NullTable lookups. Complexity: `O(popcount(size))` hash
operations.

**Complexity of subtree_root:** Each recursive call either terminates via
a stored node lookup / NullTable lookup (O(1)), or splits into two
subproblems where at least one child terminates. The proof path requires
at most `⌈log₂(n)⌉` siblings, each resolved by a single `subtree_root`
call. Total: `O(log n)` lookups + `O(log n)` hash operations.

### §12. Proof Generation

**Definition 15** (Inclusion proof — operational). For algorithm `a` and
leaf index `index`:

```
inclusion_proof(S, a, index) =
  path(S, a, index, 0, tree_size(a))

path(S, a, m, lo, hi) =
  []                                             if hi - lo = 1
  path(S, a, m, lo, lo+k)                       if m < lo+k
    ++ [subtree_root(S, a, lo+k, hi)]
  path(S, a, m, lo+k, hi)                       if m ≥ lo+k
    ++ [subtree_root(S, a, lo, lo+k)]
  where k = largest_pow2_lt(hi - lo)
```

This is the RFC 9162 PATH algorithm (§2.1.3) with `subtree_root` replacing
materialized-array slicing. Each sibling is resolved via Definition 14c.

**Complexity:** `O(log n)` — the recursion depth is `⌈log₂(n)⌉`, and each
level performs one `subtree_root` call (O(1) lookup or NullTable).

**Definition 16** (Consistency proof — operational). For algorithm `a` and
old tree size `old_size`:

```
consistency_proof(S, a, old_size) =
  subproof(S, a, old_size, 0, tree_size(a), true)

subproof(S, a, m, lo, hi, b) =
  []                                             if m = hi - lo ∧ b
  [subtree_root(S, a, lo, hi)]                   if m = hi - lo ∧ ¬b
  subproof(S, a, m, lo, lo+k, b)                 if m ≤ k
    ++ [subtree_root(S, a, lo+k, hi)]
  subproof(S, a, m-k, lo+k, hi, false)           if m > k
    ++ [subtree_root(S, a, lo, lo+k)]
  where k = largest_pow2_lt(hi - lo)
```

This is the RFC 9162 SUBPROOF algorithm (§2.1.4) with `subtree_root`
replacing materialized-array slicing.

### §13. Theorems and Corollaries

The formal model defines structural operations on `MerkleTree α` and proves correct projection onto cryptographic digests. The following theorems are checked by the Lean 4 proof:

#### Theorem 1 (Structural Bridge Lemma)
For any list of structural trees `l`:
```
ctoRoot(l) = mth(l)
```
This shows that incremental stack root extraction is topologically identical to batch Merkle tree hashing at the structural level.

#### Theorem 2 (Projection Equivalence)
For all algorithms `a` in the activation map, the incrementally maintained root equals the batch-computed root over the projected leaf sequence:
```
root(a) = mthDigest(project(S, a))
```
This reduces multi-algorithm correctness to the correctness of single-algorithm RFC 9162 verification.

#### Theorem 3 (Temporal Binding)
For all `a` and `i` where `¬active(a, i) ∧ i < tree_size(a)`:
```
∄ d ∈ Bytes. leaf(a, d) = V(a, i)
```
No payload can produce a valid leaf hash at an inactive position, because that position is committed to `N₀(a)` and `leaf(a, d) ≠ N₀(a)` by domain separation (D-SEP).

#### Theorem 4 (Algorithm Isolation)
For any two algorithms `a, b` in the activation map operating over the same payload sequence, both projections independently yield valid RFC 9162 Merkle trees:
```
root(a) = mthDigest(project(S, a)) ∧ root(b) = mthDigest(project(S, b))
```
Their structural properties and verification paths are mathematically independent.

#### Theorem 5 (Generalized Bridge Lemma)
For any split policy `f` and merge schedule `s` that are `AppendConsistent`:
```
generalized_ctoRoot(s, l) = generalized_mth(f, l)
```
This establishes EML's equivalence theorem as a special case of a broader combinatorial property of tree decompositions (shift-reduce duality).

#### Corollary 1 (Manifest Commitment)
For any two clients `C₁`, `C₂` that accept the same Signed Tree Head (STH):
```
act_C₁ = act_C₂
```
Agreement on the STH implies agreement on the epoch topology. This corollary closes the manifest authentication loop: the shared knowledge of `act(a)` required by the elision protocol is a cryptographic consequence of STH verification.

## Validation

| Check                    | Result | Detail                                                                                                                                                                                              |
| :----------------------- | :----- | :-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Theorem 1 (Bridge Lemma) | PASS   | Proved by strong induction on length in Lean 4.                                                                                                                                                    |
| Theorem 2 (Proj-Equiv)   | PASS   | Commutativity of unique evaluation homomorphism `eval` with structural constructors under the homomorphic projection of Theorem 1.                                                                 |
| Theorem 3 (Temp-Binding) | PASS   | Follows from three-way domain separation (0x00, 0x01, 0x02) under ROM tag independence.                                                                                                            |
| Theorem 4 (Alg-Isolation) | PASS   | Proved in Lean 4; type signature guarantees independence as neither projection references the other algorithm's epochs or hash functions.                                                        |
| Theorem 5 (Gen-Bridge)   | PASS   | Proved purely combinatorially in Lean 4 for any append-consistent split policy and merge schedule.                                                                                                  |
| Corollary 1 (M-Commit)   | PASS   | Cryptographic commitment of `H_a(act(a))` in the signed STH tuple per algorithm.                                                                                                                    |
| **Internal consistency** | PASS   | No theorem contradicts another. The properties are layered: domain separation → Theorem 3, Theorem 1 → Theorem 2 → Theorem 4.                                                                      |
| **External adequacy**    | PASS   | The model captures all design constraints from the original exploration.                                                                                                                            |

### Performance Bounds

| Operation                   | Complexity            | Notes                                                        |
| :-------------------------- | :-------------------- | :----------------------------------------------------------- |
| Append (per algorithm)      | O(1) amortized        | Hash + CTO stack merge                                       |
| Append node storage         | O(1) amortized        | Per algorithm; persists sealed CTO nodes                     |
| Append (total)              | O(\|A(i)\|) amortized | Linear in active algorithm count                             |
| Algorithm addition          | O(log K) worst-case   | Null prefix peak computation                                 |
| Algorithm removal           | O(1)                  | Freeze frontier stack                                        |
| Algorithm resumption        | O(log n)              | Frontier stack reconstruction via subtree_root               |
| Root extraction (per alg)   | O(log n)              | Frontier stack fold                                          |
| STH construction            | O(|A| · log n)        | Root extraction per algorithm + manifest hash                |
| Inclusion proof (per alg)   | O(log n)              | Via subtree_root (Def. 14c); stored node + NullTable lookups |
| Consistency proof (per alg) | O(log n)              | Via subtree_root (Def. 14c); stored node + NullTable lookups |
| Null constant table         | O(log n) precompute   | Per algorithm, once                                          |
| Node storage (per alg)      | O(nᵢ)                 | One sealed node per internal tree position                   |
| Total storage               | Σ O(nᵢ)               | Leaves + nodes; nᵢ = tree_size of alg i                      |

### Proof Size Trade-off (Resolved: Elided Proofs)

In independent RFC 9162 Merkle logs, algorithm `a` active for `nₐ` appends has proof depth `O(log nₐ)`. In EML, proof depth is `O(log n)` where `n` is global tree size. If `nₐ ≪ n`, EML proofs are deeper.

**Resolution — Elided proofs.** Null subtree siblings are deterministic and need not be transmitted. The proof flow is:

1. **Server (prover):** Generates the full Merkle proof. Siblings whose entire leaf-coverage range falls outside all active epochs are null subtrees. The server omits them from the wire payload.
2. **EML client envelope:** The client knows `tree_size`, `index`, and the epoch list. It walks the virtual tree path, detects positions fully inside an inactive gap, synthesizes `Nₕ(a)` locally, and injects them into the proof array.
3. **Core verifier:** The envelope hands the rehydrated, full proof to the unmodified RFC 9162 verification function.

Wire proof size collapses to `O(log nₐ)`, neutralizing EML's only theoretical overhead while preserving verifier independence.

## Implications

### Implementation Guidance

1. **Self-contained crate.** EML is implemented as a standalone Rust crate (`eml`) with zero runtime dependencies. Hash algorithms are abstracted via a `Hasher` trait injected at runtime, and storage backends are abstracted via a `Storage` trait.

2. **Core data structure.** The EML state maps directly to:

   ```rust
   struct Log {
       storage: S,                                  // raw payloads + sealed nodes via Storage trait
       algs: BTreeMap<Alg, AlgState>,                // per-algorithm state
   }

   struct AlgState {
       epochs: Vec<(u64, u64)>,                      // disjoint epoch intervals
       stack: Vec<Vec<u8>>,                           // frontier stack
       hasher: Box<dyn Hasher>,                       // hash implementation
       null_table: NullTable,                         // precomputed Nₕ(a)
   }
   ```

   The `Storage` trait provides both leaf storage (`store_leaf`/`get_leaf`) and sealed node storage (`store_node`/`get_node`). Node entries are keyed by `(alg_id, left_index, height)` and written during CTO merges.

   `project()` is a test-only method (specification oracle) gated behind `#[cfg(test)]`. Production proof generation uses `subtree_root` (Definition 14c) which queries stored nodes directly.

3. **Manifest.** Introduce a structured manifest type that includes `global_tree_size`, per-algorithm roots, and activation metadata.

### Testing Strategy

- **Theorem 2 (Projection Equivalence):** For each algorithm, verify incremental root equals batch.
- **Theorem 3 (Temporal Binding):** Attempt inclusion proof at null position with arbitrary data; verify it fails.
- **Cross-algorithm independence:** Verify that changing data in one algorithm's active range doesn't affect another algorithm's root.
- **Algorithm addition:** Add algorithm mid-stream, verify null prefix peaks are correct by comparing against batch construction.
- **Parity:** EML proofs must verify against standard RFC 9162 verifiers — the verifier is unmodified.

### Architecture Decisions

- **Algorithm removal: freeze.** Deactivated algorithms freeze at their removal point. Zero ongoing maintenance cost. The manifest records the terminal `tree_size(a)` explicitly.

- **Proof transmission: elide null siblings.** The EML client envelope rehydrates deterministic null subtree siblings before handing to the standard RFC 9162 verifier. Wire size is `O(log nₐ)`, not `O(log n)`.

- **Manifest wire format.** The manifest's serialization format is a consumer concern (candidate: deterministic canonical serialization keyed by algorithm IDs).

### Resolved Design Questions

1. **Manifest wire format** (JSON vs. CBOR vs. other canonical form) — deferred to consumer.

`tree_size(a)`, `index`, and the epoch list, ensuring lockstep
agreement with zero wire overhead.
