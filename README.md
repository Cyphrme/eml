# EML — Epoch Merkle Log

A single [RFC 9162][rfc9162] append-only Merkle tree that supports multiple hash
algorithms over a shared topology. Algorithms activate and deactivate between
appends. A new algorithm's view of pre-activation positions consists of
deterministic null constants, enabling O(log n) algorithm addition without
retroactive computation.

Zero runtime dependencies. Algorithm-agnostic: callers inject hash
implementations via the [`Hasher`] trait.

## Problem

Systems that support multiple hash algorithms (for agility, migration, or
post-quantum transition) face a choice: maintain one tree per algorithm
(duplicating structure), or recompute history when adding a new algorithm
(expensive and sometimes impossible for append-only logs).

EML eliminates both costs. A single tree topology is shared across all
algorithms. When a new algorithm activates at position _n_, its projection of
positions 0..*n*−1 yields a deterministic null constant. Existing algorithms
are unaffected. The new algorithm immediately participates in the shared append
sequence without retroactive hashing: its frontier stack is initialized in
O(log _n_) time to the "null prefix peaks" corresponding to the binary
decomposition of the activation index _n_ (using precomputed null subtree roots).

Deactivated algorithms freeze at their removal point. Their root and tree size
remain immutable.

## How It Works

An EML log is a single data structure. Not one tree per algorithm — one shared
structure with one list of raw data entries:

```
Log<S: Storage> {
    storage: S,                              ← raw data, persisted via Storage trait
    algs: {
        SHA-256: { activation: 0, stack: [...] },
        BLAKE3:  { activation: 2, stack: [...] },
    }
}
```

When you `append("D")`, the raw bytes are persisted through the storage backend
once. Then each active algorithm hashes that data with its own hash function and
updates its own frontier stack. The raw data is shared; the hash computations
are independent.

### What each algorithm computes

Each algorithm maintains a _frontier stack_ — the running state needed to
incrementally compute a Merkle root. At any point, each algorithm has hashed
every leaf position in the log, but they hash different values depending on
whether they were active at that position:

```
Position:       0       1       2       3
Raw data:      "A"     "B"     "C"     "D"

SHA-256 sees:  S("A")  S("B")  S("C")  S("D")    ← active from 0, hashes all data
BLAKE3 sees:   null    null    B("C")  B("D")     ← active from 2, nulls before
               ^^^^    ^^^^
               BLAKE3(0x02) — a fixed constant
```

There is one tree topology — 4 leaves, same branching pattern. Each algorithm
computes its own hash at every node of that topology, yielding its own root:

```
The single tree topology:         What lives at each node:

         [ root ]                 SHA-256: Root_S    BLAKE3: Root_B
        /        \
    [01]          [23]            SHA-256: N01_S     BLAKE3: N01_B
    /  \          /  \
  [0]  [1]     [2]  [3]          SHA-256: L0..L3    BLAKE3: null,null,L2,L3
```

Each node in the tree has as many hash values as there are registered
algorithms. But these values are computed independently — SHA-256's `Root_S` is
derived entirely from SHA-256 operations. BLAKE3's `Root_B` is derived entirely
from BLAKE3 operations. They never mix.

### Content addressing with a single hash

To verify entry "C" at position 2, you pick one algorithm and work entirely
within it. Say you choose BLAKE3:

```
1. Compute the leaf hash:   leaf_hash = BLAKE3(0x00 ‖ "C")
2. Get the inclusion proof: sibling at level 0 = BLAKE3's hash of position 3
                            sibling at level 1 = BLAKE3's hash of [0,1] subtree
3. Walk the proof to the root, check against Root_B.
```

SHA-256 is not involved. Its hashes don't appear in the proof. The verifier
doesn't need to know SHA-256 exists. From the verifier's perspective, they are
checking a standard RFC 9162 Merkle tree proof — the fact that other algorithms
computed different hashes at the same positions is invisible and irrelevant.

This is why a single algorithm is sufficient to address any entry: each
algorithm's hashes form a complete, independent Merkle tree over the shared
topology. Picking an algorithm selects which column of hashes you verify
against. The other columns are inert.

### Why algorithms can't weaken each other

Every algorithm computes its own hashes from its own operations. Adding a
weak algorithm doesn't change, touch, or reference the strong algorithm's
hashes. It's like adding a column to a spreadsheet — existing columns don't
change. Verification within one column never reads another column's values.

### Why null-fill is cheap

Because every null leaf is identical, null subtrees are perfectly symmetric:

```
N₁ = H(0x01 ‖ N₀ ‖ N₀)        N₂ = H(0x01 ‖ N₁ ‖ N₁)
     /          \                    /          \
    N₀          N₀                  N₁          N₁
                                   / \          / \
                                 N₀   N₀      N₀   N₀
```

`N₁` is computed once from `N₀`. `N₂` once from `N₁`. To fill a gap of
1,000,000 positions, compute ~20 values (one per bit), not 1,000,000.
Algorithm addition is O(log n), not O(n).

## Core Concepts

**Shared topology.** One tree, many hash functions. Every algorithm sees the
same leaf positions, but computes different digests. The global tree size
governs structure; per-algorithm tree sizes may differ (frozen algorithms stop
at their deactivation index).

**Null-fill.** Positions before an algorithm's activation contain `N₀(a) =
H_a(0x02)` — a cryptographic digest computed over a single prefix byte (`0x02`)
with a prefix distinct from leaf (`0x00`) and node (`0x01`) operations. This
three-way domain separation (D-SEP) ensures null leaves cannot collide with
real data or internal nodes.

**Epochs.** Each algorithm has a vector of disjoint `(start, end)` intervals.
The initial epoch begins at activation; removal closes the current epoch;
resumption opens a new one. These epochs partition the leaf space into active
and inactive regions. The temporal binding property (T-BOUND) guarantees that
no forged payload can verify at any inactive position — whether in the null
prefix before first activation, inter-epoch gaps, or the null suffix after
final deactivation.

**Manifest commitment.** To maintain absolute independence between algorithms
and prevent downgrade or misrepresentation attacks, each algorithm's active
epoch boundaries (its manifest) are cryptographically committed to the Signed
Tree Head (STH) alongside the Merkle root. Agreement on the STH guarantees
agreement on the epoch topology, making epoch membership a cryptographic
consequence of root verification without requiring out-of-band trust
assumptions.

**Projection.** `Log::project(alg_id)` materializes the full leaf sequence for
one algorithm — null constants for inactive positions, real hashes for active
positions. This projected sequence is a standard RFC 9162 log. All proofs
operate over it directly (PROJ-VALID), so standard verifiers work without
modification.

**Isomorphic correctness.** The bottom-up, stack-based merge cascade executed
on append is mathematically guaranteed to be topologically isomorphic to RFC
9162's top-down bisection (the core theorem of the Lean 4 proof). While EML
computes roots incrementally in memory, the resulting roots and proofs are
identical to those of a standard top-down Merkle tree constructed over the
algorithm's virtual projection.

**Elided proofs.** Inclusion proofs contain null-sibling hashes that are
deterministically reconstructable by the verifier. `elide_inclusion_proof`
strips these redundant siblings, reducing wire size from O(log _n_) to O(log
_n_\_a) where _n_\_a is the algorithm's active tree size. `rehydrate_inclusion_proof`
restores the full proof client-side.

**Gap resumption.** Reactivating a frozen algorithm requires bridging the gap
of size _G_ since deactivation. EML fast-forwards the algorithm's frontier stack
in O(log _G_) time by merging the existing stack with precomputed null subtrees
(frontier extension). This allows resumed algorithms to rejoin the append loop
without O(_G_) retroactive hashing.

**Node caching.** During `append`, sealed internal nodes (complete subtree roots
computed during CTO merges) are persisted through the `Storage` backend. This
enables O(log n) proof generation via point lookups rather than O(n)
materialization. `subtree_root` resolves sibling hashes through stored-node
lookups, falling back to recursive recomputation only when a node is absent.

**Cold reconstruction.** `Log::from_storage` introduces the capability to rebuild
the full log state from a populated storage backend. Algorithm metadata (IDs, epoch boundaries)
is loaded from storage; frontier stacks are rebuilt in O(log n) per algorithm by
decomposing the tree size into binary and resolving each complete subtree root
through stored nodes. This enables process restarts without replaying the
append history.

## Usage

Implement `Hasher` for your algorithm, then:

```rust
use eml::{Log, Hasher, MemoryStorage};

let mut log = Log::new(MemoryStorage::new());
log.add_algorithm(0, Box::new(my_sha256_hasher))?;

log.append(b"first entry")?;
log.append(b"second entry")?;

let root = log.root(0)?;
let proof = log.inclusion_proof(0, 1)?; // prove leaf 1

// Add a second algorithm mid-stream:
log.add_algorithm(1, Box::new(my_blake3_hasher))?;
log.append(b"third entry")?;

// Algorithm 1 sees: [null, null, real_leaf] — three positions, two null-filled.
let root_blake3 = log.root(1)?;
```

For production, implement the `Storage` trait for your persistence layer
(database, filesystem, etc.). `MemoryStorage` is provided for testing and
small logs. On cold start, reconstruct the log from an existing storage backend
via `Log::from_storage(storage, hashers)`.

## Public API

| Type / Function             | Purpose                                                                            |
| :-------------------------- | :--------------------------------------------------------------------------------- |
| `Log<S: Storage>`           | The state machine. Append data, manage algorithms, extract proofs.                 |
| `Log::new`                  | Create an empty log with a fresh storage backend.                                  |
| `Log::from_storage`         | Reconstruct log state from a populated storage backend (cold start).               |
| `Log::into_storage`         | Consume the log and reclaim the underlying storage backend.                        |
| `Log::add_algorithm`        | Register a new hash algorithm, activating it at the current tree size.             |
| `Log::remove_algorithm`     | Deactivate (freeze) an algorithm at the current tree size.                         |
| `Log::resume_algorithm`     | Reactivate a frozen algorithm, null-filling the gap since deactivation.            |
| `Log::append`               | Append a leaf payload; updates all active algorithms' frontier stacks.             |
| `Log::root`                 | Extract the current root hash for a given algorithm.                               |
| `Log::inclusion_proof`      | Generate an RFC 9162 inclusion proof for a leaf at a given index.                  |
| `Log::consistency_proof`    | Generate an RFC 9162 consistency proof between two tree sizes.                     |
| `Log::size`                 | Return the current number of appended leaves (global tree size).                   |
| `Log::algorithms`           | Return per-algorithm metadata snapshots (manifest data).                           |
| `Storage`                   | Trait for persistence backends (leaves, sealed nodes, algorithm metadata).         |
| `MemoryStorage`             | In-memory `Storage` implementation for testing and small logs.                     |
| `MemoryStorageError`        | Error type for `MemoryStorage` (out-of-bounds leaf reads).                         |
| `Hasher`                    | Trait for hash algorithm implementations (leaf, node, empty, null). `Send + Sync`. |
| `AlgorithmInfo`             | Per-algorithm metadata snapshot (root, epoch boundaries, tree size).               |
| `NullTable`                 | Memoized null-sibling ladder (internal, but public for advanced use).              |
| `InclusionProof`            | RFC 9162 inclusion proof for a leaf at a given index.                              |
| `ConsistencyProof`          | RFC 9162 consistency proof between two tree sizes.                                 |
| `ElidedInclusionProof`      | Wire-optimized proof with null siblings stripped.                                  |
| `verify_inclusion`          | Verify an inclusion proof against a root.                                          |
| `verify_consistency`        | Verify a consistency proof between two roots.                                      |
| `elide_inclusion_proof`     | Strip null siblings from a proof (epoch-aware).                                    |
| `rehydrate_inclusion_proof` | Restore elided siblings using the algorithm's `Hasher`.                            |
| `Error`                     | Structured error type for all fallible operations.                                 |
| `Result<T>`                 | Convenience alias for `std::result::Result<T, Error>`.                             |

## Formal Verification & Model

The core algebraic correctness of EML is formally verified using the **Lean 4 interactive theorem prover**. The machine-checked proofs are located in the [`proofs/lean/`](proofs/lean/) directory (see the [Reviewer's Guide](proofs/lean/README.md) for details).

Specifically, the proofs verify:
- **Theorem 1: Structural Bridge Lemma** (`bridge_lemma`): Incremental stack root extraction is topologically identical to batch Merkle tree hashing at the structural level.
- **Theorem 2: Projection Equivalence** (`projection_equivalence`): An incremental bottom-up frontier stack fold is structurally equivalent to a top-down bisection of the full algorithm projection (RFC 9162 Merkle Tree Hash), establishing correctness of the $O(\log n)$ append/reconstruction state transitions.
- **Theorem 3: Temporal Binding** (`temporal_binding`): For any algorithm $a$, inactive tree positions before first activation, in inter-epoch gaps, or after final deactivation are bound to a domain-separated null constant $N_0(a) = H_a(0x02)$, preventing adversarial forgeries at inactive positions.
- **Theorem 4: Algorithm Isolation** (`algorithm_isolation`): Independent algorithms operating on the shared topology maintain strict state separation, preventing cross-algorithm collisions or security degradation.
- **Theorem 5: Generalized Bridge Lemma** (`generalized_bridge_lemma`): The shift-reduce duality holds in a generalized algebraic framework over free magmas, proving topology equivalence for *any* append-consistent Merkle tree layout.

Key laws verified by the test suite:

| Law               | Property                                                       |
| :---------------- | :------------------------------------------------------------- |
| A-EQUIV           | Incremental root equals batch `mth()` over the projection      |
| A-STACK           | Frontier stack length equals `popcount(tree_size)`             |
| I-SOUND           | Inclusion proofs verify for correct leaves, reject forged ones |
| K-SOUND           | Consistency proofs verify between any valid old/new size pair  |
| T-BOUND           | Forged payloads at null positions fail verification            |
| D-SEP             | `leaf(d) ≠ null()`, `leaf(d) ≠ node(l, r)` for all inputs      |
| PROJ-VALID        | Projected sequence is a valid RFC 9162 log                     |
| STATE-MACHINE     | Multi-hasher interleaving preserves all invariants per-step    |
| ALG-IND           | Distinct hashers produce distinct roots for identical data     |
| FROZEN-BOUNDS     | Frozen algorithm proof domain is correctly bounded             |
| ELIDE-WIRE-LEN    | Elided proof wire length ≤ full proof length, roundtrip holds  |
| ELIDE-MULTI-EPOCH | Elision/rehydration correct across disjoint active epochs      |

## Testing

75 tests across four categories:

- **Unit tests (52):** Targeted tests for individual operations — append
  semantics, algorithm lifecycle, proof generation, null-fill, and cold
  reconstruction via `from_storage`.
- **Property-based tests (16):** [proptest]-driven verification of equational
  laws over thousands of randomly generated tree configurations, including a
  comprehensive state machine test that exercises arbitrary interleavings of
  add, remove, resume, and append operations.
- **Fault injection tests (7):** Adversarial storage backends that corrupt
  node hashes (bit-flip, drop) to verify that tampered proofs are reliably
  rejected. Includes 2 property-based corruption tests.
- **Complexity regression tests (6):** Empirical curve-fitting against
  performance bounds from the formal model (O(log n) proofs, O(1) amortized
  append, O(log K) algorithm addition, O(G) gap resumption). Gated behind
  release profile.

```sh
cargo test                              # unit + proptest + fault injection
cargo test --release --test complexity  # complexity regression
```

### Fuzz targets

5 [cargo-fuzz] harnesses exercise adversarial inputs against the proof
verification, elision, and stateful transition surfaces:

- `verify_inclusion` — arbitrary inclusion proof / root pairs
- `verify_consistency` — arbitrary consistency proof / root pairs
- `rehydrate_proof` — arbitrary elided proofs through rehydration
- `proof_mutation` — single-bit mutations of valid proofs (up to 65,536 leaves)
- `state_machine` — stateful API transition command sequences and storage write-fault injection with reconstruction crash-recovery validation

```sh
cargo +nightly fuzz run <target>
```

## Status

The logical model and in-memory implementation of EML are stable and formally verified. The data structure specification is mathematically complete and stable. However, the persistence API (`Storage` trait) and its storage backends remain experimental until persistent database implementations are integrated and production-tested.

## License

Copyright © 2026 [Cyphrme](https://github.com/Cyphrme). All rights reserved.

This source code is distributed under an interim license that permits non-commercial, personal, academic, or research use. Commercial use is strictly prohibited. See the [LICENSE](./LICENSE) file for the complete terms.

[rfc9162]: https://datatracker.ietf.org/doc/html/rfc9162
[proptest]: https://crates.io/crates/proptest
[cargo-fuzz]: https://crates.io/crates/cargo-fuzz
