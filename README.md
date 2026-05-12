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

## Core Concepts

**Shared topology.** One tree, many hash functions. Every algorithm sees the
same leaf positions, but computes different digests. The global tree size
governs structure; per-algorithm tree sizes may differ (frozen algorithms stop
at their deactivation index).

**Null-fill.** Positions before an algorithm's activation contain `N₀(a) =
H_a(0x02)` — a single-byte hash with a prefix distinct from leaf (`0x00`) and
node (`0x01`) operations. This three-way domain separation (D-SEP) ensures null
leaves cannot collide with real data or internal nodes.

**Epochs.** Each algorithm has an activation index and an optional deactivation
index. These partition the leaf space into a null prefix and an active suffix. The temporal binding property (T-BOUND) guarantees that no
forged payload can verify at a null position.

**Projection.** `Log::project(alg_id)` materializes the full leaf sequence for
one algorithm — null constants for the prefix, real hashes for the suffix. This
projected sequence is a standard RFC 9162 log. All proofs operate over it
directly (PROJ-VALID), so standard verifiers work without modification.

**Elided proofs.** Inclusion proofs contain null-sibling hashes that are
deterministically reconstructable by the verifier. `elide_inclusion_proof`
strips these redundant siblings, reducing wire size from O(log _n_) to O(log
_n_\_a) where _n_\_a is the algorithm's active tree size. `rehydrate_inclusion_proof`
restores the full proof client-side.

## Usage

Implement `Hasher` for your algorithm, then:

```rust
use tsml::{Log, Hasher};

let mut log = Log::new();
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

## Public API

| Type / Function             | Purpose                                                               |
| :-------------------------- | :-------------------------------------------------------------------- |
| `Log`                       | The state machine. Append data, manage algorithms, extract proofs.    |
| `Hasher`                    | Trait for hash algorithm implementations (leaf, node, empty, null).   |
| `AlgorithmInfo`             | Per-algorithm metadata snapshot (root, epoch boundaries, tree size).  |
| `NullTable`                 | Memoized null-sibling ladder (internal, but public for advanced use). |
| `InclusionProof`            | RFC 9162 inclusion proof for a leaf at a given index.                 |
| `ConsistencyProof`          | RFC 9162 consistency proof between two tree sizes.                    |
| `ElidedInclusionProof`      | Wire-optimized proof with null siblings stripped.                     |
| `verify_inclusion`          | Verify an inclusion proof against a root.                             |
| `verify_consistency`        | Verify a consistency proof between two roots.                         |
| `elide_inclusion_proof`     | Strip null siblings from a proof.                                     |
| `rehydrate_inclusion_proof` | Restore elided siblings using the algorithm's `Hasher`.               |
| `Error`                     | Structured error type for all fallible operations.                    |

## Formal Model

The implementation follows a 16-definition algebraic model with 9 equational
laws. The full specification is in
[`docs/models/temporally-sparse-merkle-log.md`](docs/models/temporally-sparse-merkle-log.md).

Key laws verified by the test suite:

| Law        | Property                                                       |
| :--------- | :------------------------------------------------------------- |
| A-EQUIV    | Incremental root equals batch `mth()` over the projection      |
| A-STACK    | Frontier stack length equals `popcount(tree_size)`             |
| I-SOUND    | Inclusion proofs verify for correct leaves, reject forged ones |
| K-SOUND    | Consistency proofs verify between any valid old/new size pair  |
| T-BOUND    | Forged payloads at null positions fail verification            |
| D-SEP      | `leaf(d) ≠ null()`, `leaf(d) ≠ node(l, r)` for all inputs      |
| PROJ-VALID | Projected sequence is a valid RFC 9162 log                     |

## Testing

43 tests: 33 targeted unit tests and 10 property-based tests ([proptest]) that
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
