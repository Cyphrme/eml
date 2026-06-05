# NEML: N-ary Epoch Merkle Log

`neml` is a Rust library implementing the **N-ary Epoch Merkle Log (NEML)** — a unified append-only Merkle log that combines epoch-based multi-algorithm lifecycle management with arbitrary-arity recursive subtrees.

---

## Motivation

Traditional append-only Merkle logs (such as RFC 6962 / RFC 9162 Certificate Transparency logs) append flat, unstructured entries. If the application's data is internally structured — for example, a batch of operations grouped into transactions, and transactions grouped into a block — that structure must either be flattened into individual leaf appends, or managed via a separate Merkle tree whose root is then appended to the log.

The second approach creates a **structural seam**: verifying that a specific leaf belongs to the log requires two disjoint proofs (one inside the local data tree, one inside the global log), with separate verification logic for each.

`neml` eliminates this seam. A single `InclusionProof` walks from an individual leaf, up through the arbitrarily-structured subtree that contains it, and into the global log — as one uniform path.

---

## How It Works

`neml` is a **tree of trees**: a fixed-arity Merkle log with arbitrary-arity recursive subtrees attached at the leaves.

```text
                     [Log Root]                  <-- Log Level: Fixed Arity k=2
                     /        \
                    /          \
                  R_0          R_1               <-- Subtree Roots
                /  |  \      / / | \ \
               /   |   \    / /  |  \ \
              A    B    C  D  E  F   G  H        <-- Subtree Internals (Arity 3 and 5)
             / \
            /   \
          A_1   A_2                              <-- Nested (Arbitrary Depth)
```

**Subtree level (dynamic arity):** Each append is a recursive `Subtree` value. Internal nodes can have any number of children — 2, 5, 100 — determined entirely by the data:

```rust
pub enum Subtree {
    Leaf(Vec<u8>),
    Node(Vec<Subtree>),
}
```

**Log level (fixed arity):** The log accumulates subtree roots into a single global history using a fixed arity $k$ (default 2) and a deterministic base-$k$ carry-reduction schedule. This is a direct generalization of the binary carry schedule used by Crosby-Wallach history trees and Certificate Transparency.

**Why separate them?** Consistency proofs (proving the log at size $m$ is an append-only prefix of size $n$) require a deterministic, predictable tree topology. By keeping the log-level arity fixed and deterministic, `neml` preserves standard $O(\log n)$ consistency proofs while giving the application complete freedom over the internal structure of each append.

---

## Epochs & Multi-Algorithm Support

A Merkle log is typically bound to a single hash algorithm for its entire lifetime. Migrating to a new algorithm means starting a new log identity — fragmenting the timeline and forcing auditors to reconcile multiple independent logs.

`neml` solves this with **epochs**. Multiple hash algorithms can coexist within a single log over a shared topology. Each algorithm maintains its own frontier stack, its own internal node hashes, and its own root — but all algorithms observe the same leaf positions, the same tree structure, and the same append order.

An algorithm's lifetime is partitioned into **epochs**: disjoint intervals during which it actively hashes appended data. Between epochs, the algorithm is frozen: its root is immutable, and new appends produce null constants in its projection.

Three operations govern algorithm lifecycles:
- **`add_algorithm`**: Register a new algorithm at the current tree size. Its frontier is initialized from null constants in $O(\log n)$.
- **`remove_algorithm`**: Freeze an algorithm at the current tree size. Future appends do not update it.
- **`resume_algorithm`**: Reactivate a frozen algorithm. Its frontier is reconstructed from stored nodes and null constants in $O(\log n)$.

From the perspective of a verifier holding a single algorithm's root and proof, `neml` is indistinguishable from a standard single-algorithm Merkle tree. Other algorithms' hashes are invisible.

For detailed formal treatment of the epoch model, see the [EML paper](https://eml-paper.netlify.app/), which defines the Polymorphic Merkle Log paradigm that NEML generalizes to n-ary topologies.

---

## Key Properties

**Singleton promotion.** If an internal node has exactly one child, it is promoted directly without hashing: $E(\text{Node}([c])) = E(c)$. Degenerate single-child chains collapse to a single evaluation, eliminating unnecessary hash operations.

**Flat null promotion.** All fully-null subtrees — regardless of height — evaluate to a single constant $N_0 = H(\mathtt{0x02})$. Unlike height-dependent null tables (as used in EML's binary model), `neml` uses a flat null constant: if every child of a node is $N_0$, the parent is also $N_0$. This eliminates precomputed null tables entirely.

**Seamless inclusion paths.** A single `InclusionProof` is a flat sequence of `ProofStep` values. Each step specifies sibling hashes and the position of the path node among them. The verifier processes steps uniformly — it does not need to know whether a given step originated inside a subtree or at the log level.

**Atomic batch writes.** All storage mutations from a single append (leaf data, internal nodes, log-level reductions) are written as a single atomic batch, ensuring crash-recovery consistency.

---

## Security Model

### Content Addressing & Prefix-Free Hashing

`neml` uses **prefix-free hashing** — no `0x00` or `0x01` domain separation tags on leaves or nodes. The motivation is **content addressing**: leaf hashes should be standard cryptographic hashes of the data ($H(\text{data})$), independently verifiable as content identifiers without translation. Prefixed leaves ($H(\mathtt{0x00} \parallel \text{data})$) are not standard content hashes and cannot be verified outside the context of the specific Merkle tree that produced them.

### Second-Preimage Protection via Topological Commitments

Standard Merkle trees use prefix bytes to prevent second-preimage attacks (e.g., an adversary presenting an internal node's hash input as a leaf payload). Without prefixes, `neml` prevents this structurally via **topological commitments**:

- The signed tree head commits to the tree size $n$ and the arity configuration.
- A left-filled tree's structure is a bijection of its size and arity — given $n$ and $k$, there is exactly one valid topology.
- The verifier reconstructs the expected topology and asserts that the proof structure matches. Any attempt to substitute a leaf for an internal node, or to alter a node's arity, produces a topology mismatch and is rejected.

### Null Domain Isolation

The null constant $N_0 = H(\mathtt{0x02})$ uses a dedicated domain prefix (`0x02`). A standard internal node's hash preimage is a concatenation of $m$ digests, totaling $m \cdot B$ bytes (where $B$ is the digest size, e.g. 32 for SHA-256). Since $m \geq 2$, the minimum preimage length of a standard node is $2B = 64$ bytes. The preimage of $N_0$ is 1 byte. These lengths are strictly disjoint, so under a collision-resistant hash function, the null constant can never collide with a standard node hash.

---

## Literature Foundations

**Crosby-Wallach history trees.** The log-level carry-reduction schedule generalizes Crosby & Wallach's (2009) *Efficient Data Structures for Tamper-Evident Logging*, which provides the $O(\log_k n)$ append-only consistency and inclusion proof model underlying Certificate Transparency (RFC 9162). For $k=2$, this reduces to the standard binary model.

**Nested Merkle commitments.** Embedding dynamic-arity subtrees inside a fixed-arity log is structurally analogous to the block-transaction decoupling in distributed ledgers. For example, Ethereum's block header chain forms a linear history, but each block commits to the root of a Merkle Patricia Trie (a 16-ary tree). `neml` formalizes this pattern into a single library with a unified proof path, rather than requiring separate codebases and proof models for each layer.

**Epoch-based algorithm agility.** The multi-algorithm epoch model is defined formally in the [EML paper](https://eml-paper.netlify.app/) under the Polymorphic Merkle Log (PML) paradigm. NEML extends this model from binary topologies to configurable $k$-ary topologies with dynamic-arity subtree appends.

---

## Soundness & Complexity

### Consistency Proofs

Consistency proofs (proving the log at size $m$ is an append-only prefix of size $n$) only traverse log-level nodes. This is sound because each appended subtree is reduced to a single root hash $R_i$ before entering the log. By collision resistance, $R_i$ uniquely commits to the subtree's contents. Proving that the sequence $R_0, \ldots, R_{m-1}$ is unchanged also proves the historical subtrees are unmodified.

Consistency proof size is $O(\log_k n)$ where $n$ is the number of appends and $k$ is the log-level arity. This bound holds regardless of subtree structure.

### End-to-End Inclusion Proofs

Inclusion proofs for a leaf nested inside a subtree must traverse **both** the subtree internals and the log-level tree. The proof path walks from the leaf up through the subtree (reconstructing the subtree root $R_i$), then continues through the log-level nodes (reconstructing the global root from $R_i$). Every step is linked via the hash function, forming an unbroken chain of commitments from the leaf to the global root.

The actual complexity of an end-to-end inclusion proof is:

$$O(d + \log_k n)$$

where $d$ is the depth of the target leaf within its subtree and $n$ is the number of appends in the log. The subtree depth $d$ is entirely determined by the structure the caller constructed — for a balanced subtree with $m$ leaves and branching factor $b$, $d = O(\log_b m)$.

### Operation Complexity Summary

| Operation | Complexity | Notes |
|---|---|---|
| `append_leaf` | Amortized $O(1)$ | Flat leaf, log-level only |
| `append_subtree` | Amortized $O(s)$ | $s$ = number of nodes in the subtree |
| Consistency proof | $O(\log_k n)$ | Log-level only; independent of subtree structure |
| Inclusion proof (flat leaf) | $O(\log_k n)$ | Log-level only |
| Inclusion proof (within subtree) | $O(d + \log_k n)$ | $d$ = leaf depth in subtree |
| Root extraction | $O(\log_k n)$ | Frontier folding |
| `resume_algorithm` | $O(\log_k n)$ | Frontier reconstruction |

The log-level bounds ($O(\log_k n)$ and amortized $O(1)$ append) are empirically verified by the crate's complexity test suite using statistical curve fitting over growing input sizes.

---

## Quick Start

```rust
use neml::{NaryMerkleLog, Subtree, TreeConfig, Hasher};
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
    fn null(&self) -> Vec<u8>  { Sha256::digest([0x02]).to_vec() }
    fn hash(&self, data: &[u8]) -> Vec<u8> { Sha256::digest(data).to_vec() }
    fn clone_box(&self) -> Box<dyn Hasher> { Box::new(self.clone()) }
}

#[tokio::main]
async fn main() {
    let storage = neml::MemoryStorage::new();
    let config = TreeConfig { log_arity: 2 };
    let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await;

    // Append a structured subtree: two batches, one containing two leaves.
    let entry = Subtree::Node(vec![
        Subtree::Node(vec![
            Subtree::Leaf(b"payload_a".to_vec()),
            Subtree::Leaf(b"payload_b".to_vec()),
        ]),
        Subtree::Leaf(b"payload_c".to_vec()),
    ]);

    log.append_subtree(&entry).await.unwrap();
    println!("root: {}", hex::encode(log.root()));
}
```

---

## Further Reading

- [EML Paper](https://eml-paper.netlify.app/) — formal definition of the Polymorphic Merkle Log paradigm and the epoch-based multi-algorithm model that NEML generalizes.
- [RFC 9162](https://www.rfc-editor.org/rfc/rfc9162) — Certificate Transparency v2, the binary Merkle log standard.
- Crosby & Wallach, *Efficient Data Structures for Tamper-Evident Logging* (2009) — foundational history tree construction.
