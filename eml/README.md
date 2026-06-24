# eml-log — Epoch Merkle Log (append-only)

The `eml-log` crate is the **append-only engineering library** at Layer 2 of the
three-layer architecture: PMT (kernel) → EML/EMT (engineering libraries) →
instantiations. It is built directly on the `pmt` kernel. A concrete
instantiation (for example a binary log at `k = 2`) is a thin layer on top.

## What it is

EML (Epoch Merkle Log) is an append-only Merkle log whose two key properties
are:

1. **Arbitrary-arity subtree appends.** Each append is a recursive [`Subtree`]
   value. Internal nodes may have any number of children. A single
   [`InclusionProof`] walks uniformly from an individual leaf through any
   subtree structure into the global log — no proof composition seam.

2. **Multi-algorithm epoch lifecycle.** Multiple hash algorithms coexist over
   a shared leaf sequence. Each algorithm has its own frontier stack, its own
   roots, and an epoch timeline that records when it was active. The committed
   timeline is part of the combined root, so activation and deactivation
   boundaries are bound to the root and cannot be retroactively altered.

The library is parameterized essentially by the spine arity `k` alone
([`TreeConfig`]); the kernel's `Hasher` seam supplies the hash algorithm.

## Place in the 3-layer model

```
┌──────────────────────────────────────────────────────────────────────┐
│ Layer 1 — pmt (kernel)                                                │
└───────────────────────────┬──────────────────────────────────────────┘
                             │
  ┌──────────────────────────▼──────────────────┐
  │ Layer 2 — eml-log (this crate, append-only)  │   emt (mutable peer)
  │   frontier-stack carry · append_leaf/subtree  │   …
  │   consistency proofs · snapshot proof         │
  │   filling (data-required rebuild + verify)    │
  └──────────────────────────┬───────────────────┘
                              │
  ┌───────────────────────────▼──────────────────┐
  │ Layer 3 — instantiations                      │
  └──────────────────────────────────────────────┘
```

## Public surface

The kernel surface is re-exported through `eml::*` so consumers need not
also name the `pmt` crate directly.

### Building and appending

[`NaryMerkleLog`] is the main type, parameterized over a [`Storage`] backend.

| Operation | Method |
|---|---|
| Create empty log | `NaryMerkleLog::new(storage, hasher, config).await` |
| Resume from a sealed frontier | `NaryMerkleLog::resume(sealed, storage, hashers).await` |
| Reload from storage | `NaryMerkleLog::from_storage(storage, hashers).await` |
| Append a flat leaf | `log.append_leaf(data).await` |
| Append a structured subtree | `log.append_subtree(subtree).await` |
| Current combined root | `log.root()` |
| Per-algorithm member root | `log.root_for(alg_id)` |
| Seal into kernel currency | `log.seal().await` |

### Algorithm lifecycle

| Operation | Method |
|---|---|
| Register a new algorithm | `log.add_algorithm(alg_id, hasher).await` |
| Freeze an algorithm | `log.remove_algorithm(alg_id).await` |
| Reactivate a frozen algorithm | `log.resume_algorithm(alg_id).await` |

### Proofs

| Proof type | Description |
|---|---|
| [`InclusionProof`] | Leaf-to-root path; verify with [`verify_inclusion`]. |
| [`ConsistencyProof`] | Proves log at size `m` is an append-only prefix of size `n`. |
| [`CouplingProof`] | Maps a combined root to the active per-algorithm roots. |
| [`SnapshotProof`] | Aggregate proof over a [`pmt::Sealed`] commitment. |
| [`LeafProof`] | Self-contained leaf witness (bundles positional parameters). |
| [`BindingProof`] | Cross-algorithm binding-root consistency. |

### Filling

[`fill`] is the data-required rebuild: given the raw leaf sequence and a
committed binding root, it reconstructs the full readable tree and verifies it
against the root — the trustless path from a `Sealed` back to an auditable tree.

### Storage

[`Storage`] is the trait the log writes through. [`MemoryStorage`] is the
in-process implementation.

## How it works

**Log level (constant arity).** The log spine has a fixed arity `k`
(`2..=256`). For any size it decomposes into a frontier of perfect k-ary
subtrees (`frontier_for_size`), which fold into one root by repeatedly grouping
the rightmost `k`. Consistency proofs traverse the log-level nodes only and are
`O(log_k n)`.

**Subtree level (arbitrary arity).** Each append is a [`Subtree`] value —
`Leaf(data)` or `Node(children)`. An internal node may have any number of
children. The single inclusion proof path walks subtree internals via hash
chaining, then log-level nodes via topology-pinned steps — uniformly, with no
proof-composition seam.

**Canonicalization.** Every fold applies two always-on primitives from the
kernel: **promotion** (a lone child is lifted without hashing) and **collapse**
(all-null children fold to the null constant). These together ensure canonical
proof encoding: a zero-sibling step is rejected, so a fixed
`(leaf_hash, index, tree_size, root)` admits at most one accepting path.

**Epochs and the committed timeline.** The timeline of every registered
algorithm — when it was active and when it was frozen — is committed into the
combined root via `serialize_timeline`. A verifier reads activity from the
committed timeline, never by inspecting whether a digest equals the null
constant.

## Minimal usage example

```rust
use eml::{NaryMerkleLog, Subtree, TreeConfig, Hasher, MemoryStorage};
use sha2::{Digest, Sha256};

#[derive(Debug, Clone)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> { Sha256::digest(data).to_vec() }
    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for child in children { h.update(child); }
        h.finalize().to_vec()
    }
    fn empty(&self) -> Vec<u8> { Sha256::digest(b"").to_vec() }
    fn hash(&self, data: &[u8]) -> Vec<u8> { Sha256::digest(data).to_vec() }
    fn clone_box(&self) -> Box<dyn Hasher> { Box::new(self.clone()) }
}

fn main() {
    smol::block_on(async {
        let config = TreeConfig { arity: 2 };
        let mut log = NaryMerkleLog::new(
            MemoryStorage::new(),
            Box::new(Sha256Hasher),
            config,
        ).await.unwrap();

        // Append a structured subtree containing two leaves.
        let entry = Subtree::Node(vec![
            Subtree::Leaf(b"leaf-a".to_vec()),
            Subtree::Leaf(b"leaf-b".to_vec()),
        ]);
        log.append_subtree(&entry).await.unwrap();

        // Append a second flat leaf.
        log.append_leaf(b"leaf-c").await.unwrap();

        let root = log.root();
        assert!(!root.is_empty());
    });
}
```

## Security properties

**Second-preimage protection via topology pinning.** The verifier reconstructs
the canonical topology from the trusted `(tree_size, arity, index)` and checks
the proof's steps field-by-field against the canonical skeleton. `index`,
`tree_size`, and `arity` MUST come from an authenticated source (a signed tree
head or trusted checkpoint).

**Null collision is inert.** A leaf whose payload is the four bytes `"null"`
hashes to the same value as the null constant. Activity is read from the
committed epoch timeline, never inferred from a digest equaling the null
constant, so the collision is inert for any correct verifier.

**Formally verified properties (Lean 4).** The security core is machine-checked
in `proofs/lean/` (see its README). Proved properties include promotion and
collapse semantics, the null collision model, canonical inclusion proof
uniqueness, and k-ary spine completeness and soundness for any `k >= 2`.
The trust base is four axioms; every theorem is sorry-free.

## Literature foundations

- Crosby & Wallach, *Efficient Data Structures for Tamper-Evident Logging*
  (2009) — the frontier-stack (MMR) construction EML generalizes to base k.
- RFC 9162 — Certificate Transparency v2; the binary Merkle log this
  generalizes from.
- Merkle, *Secrecy, Authentication, and Public Key Systems* (1979) — the
  original hash tree.

## Further reading

- `docs/architecture.md` — the full three-layer architecture document.
- `pmt/README.md` — the kernel this library builds on.
- `emt/README.md` — the mutable peer; both exchange `pmt::Sealed`.
