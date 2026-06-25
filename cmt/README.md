# cmt — Canonical Mutable Tree

The `cmt` crate is the **single-algorithm mutable tree** over the structural
Merkle Spine (`spine`). It is the mutable peer of the append-only `cml` log;
both build on `spine` and neither depends on the other. The one currency they
exchange is the spine's general structural [`spine::Seal`].

`cmt` is **epoch-free** (D13): it carries no committed timeline and no binding
root. The cross-tree binding of its per-algorithm member roots — the binding /
combined root — is the `epoch` combinator's facet, added as a wrapper over the
structural `Seal` (`epoch(cmt)`, the Epoch Merkle Tree). `cmt` exposes each
algorithm's raw member root and the structural seal; it never folds them.

## What it is

CMT provides a positional, dense Merkle tree where any interior cell may
change after it is written. Because interior mutation is possible, CMT keeps
no frontier stack and generates no consistency proofs — the frontier's
"left subtrees are sealed" assumption is unsound under mutation.

What CMT adds over the spine:

- **Set and get** — dense positional cells addressed by flat index `0..len`.
- **Inclusion and non-membership proofs** — generated here, verified in the
  spine with `spine::verify_inclusion`.
- **Per-node multi-hash** — a cell is addressable under many algorithms at once;
  an algorithm may be added retroactively to a single cell in `O(log n)` without
  rehashing the whole tree ([`Cmt::add_algorithm_at`]). This is the structural
  materialization of N per-algorithm roots (D11); the cross-tree binding of
  those roots is `epoch`'s.
- **One-way seal** — [`Cmt::seal`] consumes the tree and produces the structural
  [`spine::Seal`] (the resumable frontier) that any append-only log can resume
  from, and that the `epoch` combinator wraps to add the binding root.

## Place in the layered model

```
┌──────────────────────────────────────────────────────────────────────┐
│ spine — the structural core (canonicalization, proof spine, Seal)     │
└───────────────────────────┬──────────────────────────────────────────┘
              ┌─────────────┴────────────────────┐
              │ cml (append-only)                 │   ┌── cmt (this crate, mutable)
              │ frontier · consistency            │   │   set/get · path-recompute
              └───────────────────────────────────┘   │   multi-hash · structural seal
                             │                         │
              ┌──────────────┴─────────────────────────┴──────────────┐
              │ epoch — the combinator: epoch(cml) / epoch(cmt),       │
              │ the activation timeline + binding root over either     │
              └────────────────────────────┬───────────────────────────┘
              ┌────────────────────────────┴──────────────────────────┐
              │ instantiations — EML / EMT / ETL (cyphr-tree, …)       │
              └────────────────────────────────────────────────────────┘
```

## Public surface

### `Config`

[`Config`] carries the one structural axis: the proof-spine arity `k`
(`2..=256`). Prefix domain separation is not a spine axis; an application that
wants it wraps the [`Hasher`] it passes in.

### `Cmt`

[`Cmt`] is the mutable tree.

| Method | What it does |
|---|---|
| `Cmt::new(config)` | Create an empty tree. |
| `register_algorithm(alg_id, hasher)` | Register a hash algorithm (`O(n)` initial materialization). |
| `set(index, payload, metadata)` | Write a cell; appends when `index == len`, overwrites when `index < len`. |
| `get(index)` | Read a payload. |
| `metadata(index)` | Read the opaque metadata channel (never interpreted by the library). |
| `len()` / `is_empty()` | Cell count. |
| `root(alg_id)` | Per-algorithm member root (the raw root the leaves authenticate against). |
| `member_roots()` | Every registered algorithm's member root, sorted by ID — the children `epoch` folds into the binding root. |
| `hasher(alg_id)` | Borrow the algorithm's own hash (lent to `epoch` for the binding fold). |
| `inclusion_proof(alg_id, index)` | Leaf digest and proof path, verifiable with `spine::verify_inclusion`. |
| `leaf_proof(alg_id, index)` | Self-contained [`spine::LeafProof`] (bundles the positional parameters). |
| `non_membership_proof(alg_id, index)` | Inclusion-of-null proof for a cell that hashes to the null constant. |
| `add_algorithm_at(alg_id, index, hasher)` | Retroactive per-node algorithm add; only the changed path is recomputed (`O(log n)`). |
| `seal()` | Consume the tree and produce the structural [`spine::Seal`] carrying the resumable frontier. |

### `Error`

[`Error`] covers construction and mutation failures:
`InvalidArity`, `DuplicateAlgorithm`, `IndexGap`, `EmptySeal`, `MalformedSeal`.

## Minimal usage example

```rust
use cmt::{Cmt, Config};
use spine::{Hasher, verify_inclusion};
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
let mut tree = Cmt::new(Config { arity: 2 }).unwrap();
tree.register_algorithm(ALG, Box::new(Sha256Hasher)).unwrap();
tree.set(0, b"hello".to_vec(), Vec::new()).unwrap();
tree.set(1, b"world".to_vec(), Vec::new()).unwrap();

// Root and inclusion proof.
let root = tree.root(ALG).unwrap();
let (leaf_hash, path) = tree.inclusion_proof(ALG, 0).unwrap();

// Verify with the spine — CMT shares the spine index space.
assert!(verify_inclusion(&Sha256Hasher, &leaf_hash, 0, tree.len(), tree.arity(), &path, &root));

// Overwrite a cell and see the root change.
tree.set(0, b"hi".to_vec(), Vec::new()).unwrap();
assert_ne!(tree.root(ALG).unwrap(), root);

// Seal: one-way into the structural Seal (epoch wraps it to add the binding root).
let sealed = tree.seal().unwrap();
assert_eq!(sealed.tree_size(), 2);
```

## Further reading

- `spine` — the structural core this library builds on.
- `cml` — the append-only peer; both exchange `spine::Seal`.
- `epoch` — the combinator that lifts `cmt` to `epoch(cmt)` (the EMT) with the
  binding root and the combined `Sealed` currency.
