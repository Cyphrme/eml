# NEML: N-ary Epoch Merkle Log

`neml` is a Rust library implementing the **N-ary Epoch Merkle Log (NEML)** — a unified append-only Merkle log that combines epoch-based multi-algorithm lifecycle management with arbitrary-arity recursive subtrees.

---

## Motivation

Traditional append-only Merkle logs (such as those defined by RFC 6962 / RFC 9162) append flat, unstructured entries. If an application's data is internally structured — a batch of operations grouped into transactions, transactions grouped into a block — that structure must either be flattened into individual leaf appends, or managed via a separate Merkle tree whose root is then appended to the log.

The second approach creates a **structural seam**: verifying that a specific leaf belongs to the log requires two disjoint proofs — one inside the local data tree, one inside the global log — with separate verification logic for each. The verifier must independently check that the inner proof's root matches the outer proof's leaf, introducing a composition boundary that is a source of implementation bugs and conceptual overhead.

`neml` eliminates this seam. A single `InclusionProof` walks from an individual leaf, up through the arbitrarily-structured subtree that contains it, and into the global log — as one uniform path.

---

## Design Tradeoffs & Protocol Motivations

NEML is designed under a different set of constraints than traditional logging protocols like Certificate Transparency (CT). While CT optimizes for lightweight, single-algorithm browser-side verification of publicly audited logs, NEML is designed to support the **Cyphr** self-sovereign identity protocol. 

Identity histories are long-lived (potentially lasting decades), meaning the cryptographic primitives securing them *must* be capable of evolving over time without breaking historical continuity or splitting the protocol's timeline.

This design shifts the balance of traditional Merkle tree tradeoffs in three key ways:

### 1. Unified Timeline vs. Storage Overhead (Polymorphism)
*   **The Tradeoff:** Maintaining a Polymorphic Merkle Log requires the storage engine to index separate node sets for each registered algorithm, increasing storage and indexing overhead.
*   **The Motivation:** Traditional logs handle algorithm migration by creating a new log identity and genesis block. For an identity protocol like Cyphr, this fragments the historical record and forces clients to reconcile disjoint cryptographic timelines. By keeping the topology uniform and binding different algorithms to a shared leaf sequence, NEML permits seamless algorithm transition.
*   **Frozen Boundary Limitation:** Because a frozen algorithm is static, append-only consistency proofs for that algorithm cannot cross its deactivation boundary. To audit append-only continuity across algorithm transitions, clients must utilize Multi-Hash Coupling to bridge transitions, verifying consistency of the active algorithm before the transition and the new algorithm after the transition, coupled via signed Combined Roots.

### 2. Null Projections as Cryptographic Inactivity Proofs
*   **The Tradeoff:** When an algorithm is frozen (inactive), appends generate flat null constants ($N_0$) in its frontier projection, occupying logical tree coordinates without hashing actual data.
*   **The Auditing Value:** In a polymorphic log, a null node within an inclusion proof constitutes an **unforgeable cryptographic proof of temporal inactivity** for that algorithm. It demonstrates to external auditors that the logger did *not* utilize the algorithm during that specific epoch, preventing retroactive algorithm substitution or backdating attacks.
*   **Epoch Schedule Trust Assumption:** Since the Combined Root only binds active algorithm roots at any size, the Combined Root itself does not commit to the inactive status of frozen algorithms. Inactivity verification depends on validating the active algorithms list via signed checkpoints, ensuring the epoch schedule cannot be retroactively altered.
*   **Storage Optimization Tradeoff:** To minimize database size, subtrees consisting entirely of null constants are omitted from storage. Consequently, node retrieval returns the null constant when a coordinate is absent. While this avoids storing sparse null frontiers, it means missing or corrupted non-null nodes within active ranges could reconstruct as nulls, which is cryptographically detected as root mismatches during checkpoint verification.

### 3. Content Addressability vs. Prefix-Based Domain Separation
*   **The Tradeoff:** RFC 6962 (CT) prepends domain separation bytes (`0x00`/`0x01`) to hash inputs to prevent second-preimage attacks. This makes leaf hashes tree-specific and unsuitable as global content addresses. NEML uses standard leaf hashes ($H(\text{data})$) to enable clean content-addressability, which shifts the second-preimage security burden to the verification of the tree's expected topology.
*   **The Motivation:** Cyphr relies on direct content-addressable storage where leaf hashes serve as stable, canonical identifiers across multiple systems. To achieve this, NEML removes prefix-based domain separation at the hash level and instead enforces **Topological Commitments** at the verification level. The verifier uses the signed tree head's `tree_size` and `log_arity` to reconstruct the exact expected shape of the tree, rejecting any proof whose topology deviates.
*   **Subtree Log Mode Limitation:** In Subtree Log Mode (`log_arity == 0`), the verifier bypasses the topological structure check to support arbitrary recursive subtrees. Because NEML uses prefix-free hashing, bypassing the topology check removes all second-preimage protection, allowing leaf-node substitution attacks. Callers using Subtree Log Mode must enforce second-preimage resistance through out-of-band protocols (e.g., prefixing leaf payloads before appending).

---

## How It Works

`neml` is a **tree of trees**. The outer layer is a Merkle log with a fixed arity $k$ (the branching factor at each internal node, default 2). The inner layer is arbitrary: each append is a recursive `Subtree` value whose internal nodes can have any number of children.

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

**Log level (fixed arity):** The log accumulates subtree roots into a single global history using a fixed arity $k$ (default 2) and a deterministic base-$k$ carry-reduction schedule. This generalizes the binary carry schedule used by Crosby-Wallach history trees.

**Why two layers?** Consistency proofs (proving the log at size $m$ is an append-only prefix of size $n$) require a deterministic, predictable tree topology — the verifier must be able to reconstruct the expected tree shape from the tree size alone. By keeping the log-level arity fixed, `neml` preserves $O(\log_k n)$ consistency proofs while giving the application complete freedom over the internal structure of each append.

---

## Epochs & Multi-Algorithm Support

A Merkle log is typically bound to a single hash algorithm for its entire lifetime. Migrating to a new algorithm means starting a new log identity — fragmenting the timeline and forcing auditors to reconcile multiple independent logs.

`neml` solves this with **epochs**. Multiple hash algorithms can coexist within a single log over a shared topology. Each algorithm maintains its own frontier stack, its own internal node hashes, and its own root — but all algorithms observe the same leaf positions, the same tree structure, and the same append order.

An algorithm's lifetime is partitioned into **epochs**: disjoint intervals during which it actively hashes appended data. Between epochs, the algorithm is frozen: its root is immutable, and new appends produce null constants in its projection.

Three operations govern algorithm lifecycles:
- **`add_algorithm`**: Register a new algorithm at the current tree size. Its frontier is initialized from null constants in $O(\log_k n)$.
- **`remove_algorithm`**: Freeze an algorithm at the current tree size. Future appends do not update it.
- **`resume_algorithm`**: Reactivate a frozen algorithm. Its frontier is reconstructed from stored nodes and null constants in $O(\log_k n)$.
  *   **Root Hash Resumption Shift:** Because updates to a frozen algorithm's frontier are skipped during appends, the algorithm's root at size $N$ remains the deactivated root $R_M$ (where $M \leq N$ is the deactivation size). When resumed at size $N$, the frontier is reconstructed by filling the inactive range $[M, N)$ with null constants $N_0$, shifting the active root from $R_M$ to the null-promoted root $R_N$. Clients must account for this root hash shift at the resumption boundary.

From the perspective of a verifier holding a single algorithm's root and proof, `neml` is indistinguishable from a standard single-algorithm Merkle tree. Other algorithms' hashes are invisible.

### Multi-Hash Coupling & Coupled Verification

To prevent **split-horizon attacks** (where a compromised or malicious logger serves different log contents under different algorithms for the same size), `neml` implements cryptographic **multi-hash coupling**:

*   **Signed Combined Roots:** For all active algorithms, their raw roots are serialized (in sorted order of algorithm ID) and hashed to produce a **Combined Root** ($CR$). If only one algorithm is active, it collapses back to the raw root (Singleton Promotion).
    *   **Frozen Algorithm Omission:** Combined Roots only bind algorithms that are active at that tree size. Frozen algorithms are excluded, meaning the Combined Root does not cryptographically bind historical frozen data. A compromised logger could tamper with historical frozen nodes in storage without violating Combined Root checks unless clients independently verify the historical checkpoints.
*   **Decoupled Verification (`CouplingProof`):** Rather than bloating standard inclusion or consistency proofs with companion algorithm roots, `neml` decouples the multi-algorithm binding. A lightweight `CouplingProof` maps the Combined Root to the active roots. The verifier validates the `CouplingProof` once to extract the trusted raw root for their target algorithm, then verifies the standard single-algorithm proof against it.
    *   **Transition Bridge Limitation:** The `verify_consistency_with_coupling` helper assumes the target algorithm is active in both states. If the algorithm's active status changes (activation or deactivation) across the boundary, the helper returns `false` because the coupling proof cannot resolve the root of the inactive algorithm. Callers must verify consistency and coupling proofs manually in this scenario.
*   **Non-Divergence Auditing (`verify_non_divergence`):** Auditors and clients can verify that parallel algorithm logs have not diverged (either in metadata or leaf data) by comparing the combined roots at historical checkpoint sizes.
*   **Coz-Compliant Checkpoints (`AuditPayload`):** Checkpoints are serialized as `AuditPayload` (containing `log_id`, `tree_size`, `active_algs`, and `combined_roots`), which is easily wrapped in Coz cryptographic envelopes to bootstrap Web of Trust consensus among validating peers.

For detailed formal treatment of the epoch model, see the [EML paper](https://eml-paper.netlify.app/), which defines the Polymorphic Merkle Log paradigm that NEML generalizes to n-ary topologies.

---

## Key Properties

**Singleton promotion.** If an internal node has exactly one child, it is promoted directly without hashing: $E(\text{Node}([c])) = E(c)$. Degenerate single-child chains collapse to a single evaluation, eliminating unnecessary hash operations.

**Flat null promotion.** All fully-null subtrees — regardless of height — evaluate to a single constant $N_0 = H(\mathtt{0x02})$. Unlike EML's binary model (which uses height-dependent null tables where $N_h = H(0x01 \| N_{h-1} \| N_{h-1})$), `neml` uses a flat null constant: if every child of a node is $N_0$, the parent is also $N_0$. This eliminates precomputed null ladders entirely.

**Seamless inclusion paths.** A single `InclusionProof` is a flat sequence of `ProofStep` values. Each step specifies sibling hashes and the index of the path node among its siblings. The verifier processes steps uniformly — it does not need to know whether a given step originated inside a subtree or at the log level.

**Atomic batch writes.** All storage mutations from a single append (leaf data, internal nodes, log-level reductions) are written as a single atomic batch, ensuring crash-recovery consistency.

---

## Security Model

### Content Addressing & Prefix-Free Hashing

`neml` uses **prefix-free hashing** — no `0x00` or `0x01` domain separation tags on leaves or nodes. Leaf hashes are standard cryptographic hashes of the data: $H(\text{data})$. This means leaf hashes are independently verifiable as content identifiers (content addresses) without knowledge of the tree that produced them. By contrast, Certificate Transparency (RFC 6962/9162) prepends `0x00` to leaf inputs and `0x01` to node inputs; these prefixed hashes are tree-specific and cannot double as content addresses.

Note: domain separation via prefix bytes is not an inherent property of Merkle trees. The original construction (Merkle, 1979) has no such mechanism. Prefix-based domain separation was introduced by Certificate Transparency as a hardening measure for its specific threat model, but it is not the only way to achieve second-preimage resistance. `neml` achieves it structurally.

### Second-Preimage Protection via Topological Commitments

The second-preimage threat in a Merkle tree is an adversary presenting an internal node's hash preimage as a leaf payload (or vice versa), causing the verifier to accept a proof for data that was never appended. RFC 6962/9162 prevent this by domain-separating hash inputs so that leaf and node preimages can never collide.

`neml` prevents this structurally via **topological commitments**:

- The signed tree head commits to the tree size $n$ and the log arity $k$.
- A left-filled $k$-ary tree's structure is a deterministic function of $n$ and $k$ — given these two values, there is exactly one valid topology (node arities and tree shape).
- The verifier reconstructs the expected topology from the signed tree head and asserts that the proof structure conforms. Any attempt to substitute a leaf for an internal node, or to alter a node's arity, produces a topology mismatch and is rejected.

This is equivalent in security to prefix-based domain separation — both ensure the verifier can distinguish leaf positions from node positions — provided the verifier has the signed tree head (which is the standard trust assumption in any append-only log protocol). The difference is where the binding happens: in the hash preimage (prefixes) vs. in the proof structure (topological commitment).

**Critical Limitation:** Topological commitments require a trusted `tree_size` and `log_arity` at the verification layer. If the verifier does not have an authenticated tree size, or if the log is verified in Subtree Log Mode (`log_arity == 0`), topological verification is bypassed. Because NEML hashes are prefix-free, second-preimage resistance is completely absent in these scenarios unless the caller enforces domain separation externally.
Additionally, verification of inclusion proofs containing nested subtree steps fails under Flat Log Mode (`log_arity >= 2`) because the subtree steps violate the uniform arity check. Thus, nested-leaf inclusion proofs must be verified using Subtree Log Mode (`log_arity == 0`), which lacks second-preimage protection.

### Selective Index & Path Verification

In an N-ary Merkle tree, inclusion proofs explicitly store the position of the target leaf and siblings at each level (`ProofStep::position`). A malicious prover could attempt to spoof the leaf's sequence number by altering `InclusionProof::index` without modifying the path (since the index field is not used in raw hash reconstruction). 

To prevent this index spoofing attack while maintaining full support for arbitrary, non-uniform subtrees, `neml` uses **Selective Index & Path Verification**:

*   **InclusionProof `log_arity` field:** The `InclusionProof` contains a `log_arity` field indicating the arity configuration of the log.
*   **Flat Log Mode (`log_arity >= 2`):** When verifying a proof from a uniform log, `log_arity` is set to the log arity (e.g. 2 or 3). The verifier performs strict structural validation (`verify_inclusion_path_structure` and `reconstruct_index_from_path`) to assert that the step positions and sibling counts match the deterministic topology for the claimed `index` and `tree_size`. If they mismatch, verification is rejected.
*   **Subtree Log Mode (`log_arity == 0`):** When verifying a proof that includes arbitrary nested subtrees (Subtree Log Mode), the log structure is non-uniform and the global leaf index cannot be deterministically verified from the path steps alone. In this case, `log_arity` is set to `0`, which tells the verifier to bypass the uniform topology check and perform standard membership/inclusion verification.
*   **Consistency Proof Exclusion:** Consistency proofs are unsupported in Subtree Log Mode. The `reconstruct_consistency_roots` verifier immediately returns `None` if `log_arity < 2`.

### Null Domain Isolation

The null constant $N_0$ represents an empty or inactive subtree. Under prefix-free hashing, defining the null digest as the output of a hash function on a known preimage would allow an attacker to input that preimage as a leaf payload and trigger a leaf-subtree substitution collision.

To prevent this collision across arbitrary hash sizes, `neml` utilizes a slice-based **Nothing-Up-My-Sleeve (NUMS) Null Stream**:

*   **Master NUMS Stream**: A 128-byte Nothing-Up-My-Sleeve high-entropy constant based on the first 256 hex digits of the fractional part of $\pi$: `0x243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89452821e638d01377be5466cf34e90c6cc0ac29b7c97c50dd3f84d5b5b54709179216d5d98979fb1bd1310ba698dfb5ac2ffd72dbd01adfb7b8e1afed6a267e96ba7c9045f12c7f9924a19947b3916cf70801f2e2858efc16636920d871574e69`.
*   **Extendable Slice Output**: For any hash algorithm with output length $L \leq 128$ bytes, the null digest is derived dynamically by slicing the first $L$ bytes of the master stream:
    $$N_0(L) = \text{take}(L, \text{Master Stream})$$
*   **Preimage Resistance**: Because the master stream is a hardcoded mathematical constant (derived from $\pi$'s fractional expansion) and not the output of the hash function itself, finding a leaf payload whose hash evaluates to $N_0(L)$ requires solving a hard hash preimage challenge. A leaf payload or internal node can never evaluate to $N_0(L)$, eliminating flat null promotion collision risk. We prove this property formally in our Lean 4 proof system.

---

## Literature Foundations

**Crosby-Wallach history trees.** The log-level carry-reduction schedule generalizes Crosby & Wallach's (2009) *Efficient Data Structures for Tamper-Evident Logging*, which introduced the incremental frontier-stack construction for append-only hash trees. Certificate Transparency (RFC 6962/9162) adopted a structurally similar binary Merkle tree. `neml` generalizes the carry schedule from base-2 to base-$k$; for $k=2$ it reduces to the standard binary model.

**Nested Merkle commitments.** Embedding dynamic-arity subtrees inside a fixed-arity log is structurally analogous to the block-transaction decoupling in distributed ledgers. For example, Ethereum's block header chain forms a linear history, but each block commits to the root of a Merkle Patricia Trie (a 16-ary tree). `neml` formalizes this pattern into a single library with a unified proof path, rather than requiring separate codebases and proof models for each layer.

**Epoch-based algorithm agility.** The multi-algorithm epoch model is defined formally in the [EML paper](https://eml-paper.netlify.app/) under the Polymorphic Merkle Log (PML) paradigm. NEML extends this model from binary topologies to configurable $k$-ary topologies with dynamic-arity subtree appends.

---

## Soundness & Complexity

### Consistency Proofs

Consistency proofs (proving the log at size $m$ is an append-only prefix of size $n$) only traverse log-level nodes. This is sound because each appended subtree is reduced to a single root hash $R_i$ before entering the log. Under collision resistance, finding two distinct subtrees with the same root hash $R_i$ is computationally infeasible, so $R_i$ binds the subtree's contents. Proving that the sequence $R_0, \ldots, R_{m-1}$ is unchanged also proves the historical subtrees are unmodified.

Consistency proof size is $O(\log_k n)$ where $n$ is the number of appends and $k$ is the log-level arity. This bound holds regardless of subtree structure.

### End-to-End Inclusion Proofs

Inclusion proofs for a leaf nested inside a subtree must traverse **both** the subtree internals and the log-level tree. The proof path walks from the leaf up through the subtree (reconstructing the subtree root $R_i$), then continues through the log-level nodes (reconstructing the global root from $R_i$). Every step is linked via the hash function, forming an unbroken chain of commitments from the leaf to the global root.
*   **Verification Mode Restriction:** Because subtree depths and arities are non-uniform, end-to-end inclusion proofs for nested leaves cannot be verified under Flat Log Mode (`log_arity >= 2`) and must be verified in Subtree Log Mode (`log_arity == 0`).

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

Add this to your `Cargo.toml`:
```toml
[dependencies]
neml = { path = "path/to/neml" } # or version
sha2 = "0.10"
smol = "2.0"
```

Implement a `Hasher` and initialize a log using `smol::block_on` (the library is async-runtime agnostic):
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
    fn null(&self) -> Vec<u8>  { neml::NULL_DIGEST.to_vec() }
    fn hash(&self, data: &[u8]) -> Vec<u8> { Sha256::digest(data).to_vec() }
    fn clone_box(&self) -> Box<dyn Hasher> { Box::new(self.clone()) }
}

fn main() {
    smol::block_on(async {
        let storage = neml::MemoryStorage::new();
        let config = TreeConfig { log_arity: 2 };
        let mut log = NaryMerkleLog::new(storage, Box::new(Sha256Hasher), config).await.unwrap();

        // Append a structured subtree: two batches, one containing two leaves.
        let entry = Subtree::Node(vec![
            Subtree::Node(vec![
                Subtree::Leaf(b"payload_a".to_vec()),
                Subtree::Leaf(b"payload_b".to_vec()),
            ]),
            Subtree::Leaf(b"payload_c".to_vec()),
        ]);

        log.append_subtree(&entry).await.unwrap();

        // Hex encode root hash
        let root_hex: String = log.root().iter().map(|b| format!("{:02x}", b)).collect();
        println!("root: {}", root_hex);
    });
}
```

---

## Further Reading

- [EML Paper](https://eml-paper.netlify.app/) — formal definition of the Polymorphic Merkle Log paradigm and the epoch-based multi-algorithm model that NEML generalizes.
- [RFC 9162](https://www.rfc-editor.org/rfc/rfc9162) — Certificate Transparency v2, the binary Merkle log standard that introduced 0x00/0x01 domain separation.
- Crosby & Wallach, *Efficient Data Structures for Tamper-Evident Logging* (2009) — foundational history tree construction.
- Merkle, *Secrecy, Authentication, and Public Key Systems* (1979) — original hash tree construction.
