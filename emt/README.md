# emt — Epoch Merkle Tree (mutable)

The `emt` crate is the **mutable engineering library** at Layer 2 of the
three-layer architecture: PMT (kernel) → EML/EMT (engineering libraries) →
instantiations. It is the mutable peer of the append-only `eml-log` library.
Both depend on the `pmt` kernel and neither depends on the other; the one
currency they exchange is the kernel's [`pmt::Sealed`].

## What it is

EMT provides a positional, dense Merkle tree where any interior cell may
change after it is written. Because interior mutation is possible, EMT keeps
no frontier stack and generates no consistency proofs — the frontier's
"left subtrees are sealed" assumption is unsound under mutation.

What EMT adds over the kernel:

- **Set and get** — dense positional cells addressed by flat index `0..len`.
- **Inclusion and non-membership proofs** — generated here, verified in the
  kernel with `pmt::verify_inclusion`.
- **Per-node multi-hash** — a cell is addressable under many algorithms at once;
  an algorithm may be added retroactively to a single cell in `O(log n)` without
  rehashing the whole tree ([`Emt::add_algorithm_at`]).
- **One-way seal** — [`Emt::seal`] consumes the tree and produces a
  [`pmt::Sealed`] that any append-only log can resume from.

## Place in the 3-layer model

```
┌──────────────────────────────────────────────────────────────────────┐
│ Layer 1 — pmt (kernel)                                                │
└───────────────────────────┬──────────────────────────────────────────┘
                             │
              ┌──────────────┴──────────────────┐
              │ eml-log (append-only)             │   ┌── emt (this crate, mutable)
              │ …                                 │   │   set/get · path-recompute
              └──────────────────────────────────┘   │   multi-hash · seal
                                                      └──────────────────────────
              ┌──────────────────────────────────────────────────────┐
              │ Layer 3 — instantiations (cyphr-tree, …)             │
              └──────────────────────────────────────────────────────┘
```

## Public surface

### `Config`

[`Config`] carries the one structural axis: the proof-spine arity `k`
(`2..=256`). Prefix domain separation is not a kernel axis; an application that
wants it wraps the [`Hasher`] it passes in.

### `Emt`

[`Emt`] is the mutable tree.

| Method | What it does |
|---|---|
| `Emt::new(config)` | Create an empty tree. |
| `register_algorithm(alg_id, hasher)` | Register a hash algorithm (`O(n)` initial materialization). |
| `set(index, payload, metadata)` | Write a cell; appends when `index == len`, overwrites when `index < len`. |
| `get(index)` | Read a payload. |
| `metadata(index)` | Read the opaque metadata channel (never interpreted by the library). |
| `len()` / `is_empty()` | Cell count. |
| `root(alg_id)` | Per-algorithm member root. |
| `combined_root(alg_id)` | Live combined root over all registered algorithms. |
| `inclusion_proof(alg_id, index)` | Leaf digest and proof path, verifiable with `pmt::verify_inclusion`. |
| `leaf_proof(alg_id, index)` | Self-contained [`pmt::LeafProof`] (bundles the positional parameters). |
| `non_membership_proof(alg_id, index)` | Inclusion-of-null proof for a cell that hashes to the null constant. |
| `add_algorithm_at(alg_id, index, hasher)` | Retroactive per-node algorithm add; only the changed path is recomputed (`O(log n)`). |
| `seal()` | Consume the tree and produce a [`pmt::Sealed`] carrying the resumable frontier. |

### `Error`

[`Error`] covers construction and mutation failures:
`InvalidArity`, `DuplicateAlgorithm`, `IndexGap`, `EmptySeal`, `MalformedSeal`.

## Minimal usage example

```rust
use emt::{Config, Emt};
use pmt::{Hasher, verify_inclusion};
use sha2::{Digest, Sha256};

#[derive(Debug)]
struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    fn leaf(&self, data: &[u8]) -> Vec<u8> { Sha256::digest(data).to_vec() }
    fn node(&self, children: &[&[u8]]) -> Vec<u8> {
        let mut h = Sha256::new();
        for c in children { h.update(c); }
        h.finalize().to_vec()
    }
    fn empty(&self) -> Vec<u8> { Sha256::digest(b"").to_vec() }
    fn hash(&self, data: &[u8]) -> Vec<u8> { Sha256::digest(data).to_vec() }
    fn clone_box(&self) -> Box<dyn Hasher> { Box::new(Sha256Hasher) }
}

const ALG: u64 = 0;

// Build a small mutable tree.
let mut tree = Emt::new(Config { arity: 2 }).unwrap();
tree.register_algorithm(ALG, Box::new(Sha256Hasher)).unwrap();
tree.set(0, b"hello".to_vec(), Vec::new()).unwrap();
tree.set(1, b"world".to_vec(), Vec::new()).unwrap();

// Root and inclusion proof.
let root = tree.root(ALG).unwrap();
let (leaf_hash, path) = tree.inclusion_proof(ALG, 0).unwrap();

// Verify with the kernel — EMT shares the kernel index space.
assert!(verify_inclusion(&Sha256Hasher, &leaf_hash, 0, tree.len(), tree.arity(), &path, &root));

// Overwrite a cell and see the root change.
tree.set(0, b"hi".to_vec(), Vec::new()).unwrap();
assert_ne!(tree.root(ALG).unwrap(), root);

// Seal: one-way into the kernel commitment currency.
let sealed = tree.seal().unwrap();
assert_eq!(sealed.tree_size(), 2);
```

## Further reading

- `docs/architecture.md` — the full three-layer architecture document.
- `pmt/README.md` — the kernel this library builds on.
- `eml/README.md` — the append-only peer; both exchange `pmt::Sealed`.
