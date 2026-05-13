# TSML — Temporally-Sparse Merkle Log

A single [RFC 9162][rfc9162] append-only Merkle tree that supports multiple hash
algorithms over a shared topology. Algorithms activate and deactivate between
appends. A new algorithm's view of pre-activation positions consists of
deterministic null constants, enabling O(1) algorithm addition without
retroactive computation.

Zero runtime dependencies. Algorithm-agnostic: callers inject hash
implementations via the [`Hasher`] trait.

## Problem

Systems that support multiple hash algorithms (for agility, migration, or
post-quantum transition) face a choice: maintain one tree per algorithm
(duplicating structure), or recompute history when adding a new algorithm
(expensive and sometimes impossible for append-only logs).

TSML eliminates both costs. A single tree topology is shared across all
algorithms. When a new algorithm activates at position _n_, its projection of
positions 0..*n*−1 yields a deterministic null constant: a fixed-point value
derived from the algorithm's own hash function, domain-separated from real
leaves and internal nodes. Existing algorithms are unaffected. The new algorithm
immediately participates in the shared append sequence with no backfill.

Deactivated algorithms freeze at their removal point. Their root and tree size
remain immutable.

## How It Works

A TSML log is a single data structure. Not one tree per algorithm — one shared
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
H_a(0x02)` — a single-byte hash with a prefix distinct from leaf (`0x00`) and
node (`0x01`) operations. This three-way domain separation (D-SEP) ensures null
leaves cannot collide with real data or internal nodes.

**Epochs.** Each algorithm has a vector of disjoint `(start, end)` intervals.
The initial epoch begins at activation; removal closes the current epoch;
resumption opens a new one. These epochs partition the leaf space into active
and inactive regions. The temporal binding property (T-BOUND) guarantees that
no forged payload can verify at any inactive position — whether in the null
prefix before first activation, inter-epoch gaps, or the null suffix after
final deactivation.

**Projection.** `Log::project(alg_id)` materializes the full leaf sequence for
one algorithm — null constants for inactive positions, real hashes for active
positions. This projected sequence is a standard RFC 9162 log. All proofs
operate over it directly (PROJ-VALID), so standard verifiers work without
modification.

**Elided proofs.** Inclusion proofs contain null-sibling hashes that are
deterministically reconstructable by the verifier. `elide_inclusion_proof`
strips these redundant siblings, reducing wire size from O(log _n_) to O(log
_n_\_a) where _n_\_a is the algorithm's active tree size. `rehydrate_inclusion_proof`
restores the full proof client-side.

## Usage

Implement `Hasher` for your algorithm, then:

```rust
use tsml::{Log, Hasher, MemoryStorage};

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
small logs.

## Public API

| Type / Function             | Purpose                                                               |
| :-------------------------- | :-------------------------------------------------------------------- |
| `Log<S: Storage>`           | The state machine. Append data, manage algorithms, extract proofs.    |
| `Storage`                   | Trait for leaf persistence backends (store/retrieve raw payloads).    |
| `MemoryStorage`             | In-memory `Storage` implementation for testing and small logs.        |
| `Hasher`                    | Trait for hash algorithm implementations (leaf, node, empty, null).   |
| `AlgorithmInfo`             | Per-algorithm metadata snapshot (root, epoch boundaries, tree size).  |
| `NullTable`                 | Memoized null-sibling ladder (internal, but public for advanced use). |
| `InclusionProof`            | RFC 9162 inclusion proof for a leaf at a given index.                 |
| `ConsistencyProof`          | RFC 9162 consistency proof between two tree sizes.                    |
| `ElidedInclusionProof`      | Wire-optimized proof with null siblings stripped.                     |
| `verify_inclusion`          | Verify an inclusion proof against a root.                             |
| `verify_consistency`        | Verify a consistency proof between two roots.                         |
| `elide_inclusion_proof`     | Strip null siblings from a proof (epoch-aware).                       |
| `rehydrate_inclusion_proof` | Restore elided siblings using the algorithm's `Hasher`.               |
| `Error`                     | Structured error type for all fallible operations.                    |

## Formal Model

The implementation follows an 18-definition algebraic model with 9 equational
laws. The full specification is in
[`docs/models/temporally-sparse-merkle-log.md`](docs/models/temporally-sparse-merkle-log.md).

Key laws verified by the test suite:

| Law            | Property                                                       |
| :------------- | :------------------------------------------------------------- |
| A-EQUIV        | Incremental root equals batch `mth()` over the projection      |
| A-STACK        | Frontier stack length equals `popcount(tree_size)`             |
| I-SOUND        | Inclusion proofs verify for correct leaves, reject forged ones |
| K-SOUND        | Consistency proofs verify between any valid old/new size pair  |
| T-BOUND        | Forged payloads at null positions fail verification            |
| D-SEP          | `leaf(d) ≠ null()`, `leaf(d) ≠ node(l, r)` for all inputs      |
| PROJ-VALID     | Projected sequence is a valid RFC 9162 log                     |
| STATE-MACHINE  | Random multi-algorithm interleaving preserves all invariants   |
| FROZEN-BOUNDS  | Frozen algorithm proof domain is correctly bounded             |
| ELIDE-WIRE-LEN | Elided proof wire length matches epoch-overlap count           |

## Testing

55 tests: 42 targeted unit tests and 13 property-based tests ([proptest]) that
exercise the equational laws over thousands of randomly generated tree
configurations.

```sh
cargo test
```

## Status

Pre-alpha. The data structure specification is experimental. Backwards
compatibility is not a concern until the formal model stabilizes.

## License

Copyright © 2026 [Cyphrme](https://github.com/Cyphrme). All rights reserved.

This source code is published for review and reference. No license is granted
for use, modification, or distribution. A formal license will be adopted when
the project reaches stability.

[rfc9162]: https://datatracker.ietf.org/doc/html/rfc9162
[proptest]: https://crates.io/crates/proptest
