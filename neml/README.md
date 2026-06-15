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
*   **The Auditing Value:** In a polymorphic log, inactivity is a verifiable claim: the per-algorithm epoch timeline is committed into the Combined Root, and a verifier reads `active(X, p)` from that committed timeline — never by inspecting whether a digest equals the null constant (a leaf payload of the literal bytes `null` hashes to the null constant by construction, and is perfectly legal). Combined with the one-directional consistency check (a position the committed epochs mark inactive must be the null constant in that algorithm's tree), this prevents retroactive algorithm substitution, repudiation, and backdating attacks.
*   **Epoch Schedule Commitment:** Because the timeline is inside the Combined Root's hash coverage, two histories that differ only in epoch boundaries produce different roots — the epoch schedule cannot be retroactively altered or substituted under a fixed root, including the "deactivated at the idle tip" case that tree cells alone cannot witness.
*   **Storage Optimization Tradeoff:** To minimize database size, subtrees consisting entirely of null constants are omitted from storage. Consequently, node retrieval returns the null constant when a coordinate is absent. While this avoids storing sparse null frontiers, it means missing or corrupted non-null nodes within active ranges could reconstruct as nulls, which is cryptographically detected as root mismatches during checkpoint verification.

### 3. Content Addressability vs. Prefix-Based Domain Separation
*   **The Tradeoff:** RFC 6962 (CT) prepends domain separation bytes (`0x00`/`0x01`) to hash inputs to prevent second-preimage attacks. This makes leaf hashes tree-specific and unsuitable as global content addresses. NEML uses standard leaf hashes ($H(\text{data})$) to enable clean content-addressability, which shifts the second-preimage security burden to the verification of the tree's expected topology.
*   **The Motivation:** Cyphr relies on direct content-addressable storage where leaf hashes serve as stable, canonical identifiers across multiple systems. To achieve this, NEML removes prefix-based domain separation at the hash level and instead enforces **Topological Commitments** at the verification level. The verifier uses the signed tree head's `tree_size` and `log_arity` to reconstruct the exact expected shape of the log-level tree, rejecting any proof whose log-level topology deviates. Because the verifier dynamically computes the log skeleton height from the frontier structure, a single verification path handles both flat-leaf and nested-subtree inclusion proofs uniformly — subtree-internal steps are verified purely by hash chaining, and log-level steps are verified topologically.

---

## How It Works

`neml` is a **tree of trees**. The outer layer is a Merkle log with a fixed arity $k$ (the branching factor at each internal node; $2 \leq k \leq 256$, default 2). The inner layer is arbitrary: each append is a recursive `Subtree` value whose internal nodes can have any number of children.

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

*   **Combined Roots (Metaroots):** The Combined Root ($CR$) is a structural metaroot layer: like any node it commits what is below it, except it spans every algorithm's tree. Its preimage serializes the raw roots of all active algorithms (in sorted order of algorithm ID) **and the committed epoch timeline of every registered algorithm** — activation/deactivation boundaries are part of the multi-algorithm structure, since they decide which cells are null projections. The metaroot is the hash of this canonical preimage, with one disciplined exception — **Genesis Promotion**: while the registry has only ever contained one algorithm and its timeline is the forced default (active from position 0, still open), the preimage carries zero information beyond the raw root, so the metaroot promotes to the raw root — the same discipline as singleton node promotion (hash only when hashing adds binding information). Any lifecycle event — registering a second algorithm, deactivating at the tip, or any deactivate/resume — makes the timeline information-bearing and permanently switches the metaroot to the hashed form. Promotion is keyed on the *registry*, never on the currently-active set: an algorithm that is merely the only active one may carry a pre-activation null prefix, which is precisely the case the timeline commitment exists to bind.
    *   **Frozen Algorithm Root Omission:** Combined Roots bind the raw roots only of algorithms active at that tree size. A frozen algorithm's root is excluded — but its full epoch timeline remains committed, so its activity ranges (including "retired as of this size") stay bound to the root. Historical frozen *node data* is not bound; clients audit it via historical checkpoints.
*   **Decoupled Verification (`CouplingProof`):** Rather than bloating standard inclusion or consistency proofs with companion algorithm roots, `neml` decouples the multi-algorithm binding. A lightweight `CouplingProof` maps the Combined Root to the active roots. The verifier validates the `CouplingProof` once to extract the trusted raw root for their target algorithm, then verifies the standard single-algorithm proof against it.
    *   **Transition Bridge Limitation:** The `verify_consistency_with_coupling` helper assumes the target algorithm is active in both states. If the algorithm's active status changes (activation or deactivation) across the boundary, the helper returns `false` because the coupling proof cannot resolve the root of the inactive algorithm. Callers must verify consistency and coupling proofs manually in this scenario.
*   **Inactivity Verification (`verify_inactivity_with_coupling`):** The claim "algorithm $X$ was inactive at position $p$" is verified directly from the Combined Root: the coupling proof authenticates the committed epoch timeline, the timeline must mark the position inactive, and — if the algorithm has a committed root at that size — a null-constant inclusion proof at that position must verify against it (the `inactive ⇒ N₀` consistency check). For a frozen algorithm the authenticated timeline alone is the evidence.
*   **Non-Divergence Auditing (`verify_non_divergence`):** Auditors and clients can verify that parallel algorithm logs have not diverged (either in metadata or leaf data) by comparing the combined roots at historical checkpoint sizes.
*   **Coz-Compliant Checkpoints (`AuditPayload`):** Checkpoints are serialized as `AuditPayload` (containing `log_id`, `tree_size`, `active_algs`, `combined_roots`, and the committed epoch timeline `alg_epochs` of every registered algorithm), which is easily wrapped in Coz cryptographic envelopes to bootstrap Web of Trust consensus among validating peers. Carrying the timeline in the payload lets the signing attestation cover activation/deactivation boundaries, making activity claims non-equivocable.

For detailed formal treatment of the epoch model, see the [EML paper](https://eml-paper.netlify.app/), which defines the Polymorphic Merkle Log paradigm that NEML generalizes to n-ary topologies.

---

## Key Properties

**Singleton promotion.** If an internal node has exactly one child, it is promoted directly without hashing: $E(\text{Node}([c])) = E(c)$. Degenerate single-child chains collapse to a single evaluation, eliminating unnecessary hash operations.

**Flat null promotion.** All fully-null subtrees — regardless of height — evaluate to a single constant $N_0 = H(\texttt{"null"})$ (see [The Null Constant](#the-null-constant--authenticated-inactivity-design-a) below). Unlike EML's binary model (which uses height-dependent null tables where $N_h = H(0x01 \| N_{h-1} \| N_{h-1})$), `neml` uses a flat null constant: if every child of a node is $N_0$, the parent is also $N_0$. This eliminates precomputed null ladders entirely.

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

**Critical Limitation:** Topological commitments require a trusted `tree_size` and `log_arity` at the verification layer. If the verifier does not have an authenticated tree size, topological verification cannot be performed and second-preimage resistance is absent unless the caller enforces domain separation externally. The verifier always requires `log_arity >= 2`; there is no bypass mode.

### Selective Index & Path Verification

In an N-ary Merkle tree, inclusion proofs explicitly store the position of the target leaf and siblings at each level (`ProofStep::position`). 

To prevent index spoofing attacks while maintaining full support for arbitrary, non-uniform subtrees, `neml` uses **Selective Index & Path Verification** with trusted parameters:

*   **Decoupled Structs:** The `InclusionProof` and `ConsistencyProof` structs do not contain metadata fields like `index`, `tree_size`, `old_size`, `new_size`, or `log_arity`. Instead, these metadata fields are passed as trusted parameters directly to the verifier functions (`verify_inclusion` and `verify_consistency`) from an authenticated Signed Tree Head (STH) or trusted checkpoint.
*   **Unified Verification:** The verifier always requires a valid `log_arity` ($2 \leq k \leq 256$, the same bounds the constructor enforces). Given the trusted `index`, `tree_size`, and `log_arity`, the shared topology module (`topology::inclusion_skeleton`) derives the expected **log skeleton** — its length and, per step, the path node's position and sibling count. The proof path is dynamically split: its trailing steps are compared field-by-field against the skeleton, while any leading steps are the **subtree portion**, verified purely by hash chaining (cryptographic membership) without topological assertions, since subtree arities are application-defined and non-uniform. The same module drives proof *generation*, so the producer and verifier cannot drift into disagreeing topologies.
*   **Why this is sound:** The log-level topological check anchors the proof to the signed tree head's committed structure. The subtree portion does not need independent topological verification because it terminates at a subtree root $R_i$ whose position in the log skeleton *is* topologically verified — the hash chain is unbroken from leaf to root, and any forgery in the subtree steps would produce a root mismatch at the log-level boundary.
*   **Canonical proof encoding:** Every accepted step must hash — it carries at least one sibling. A zero-sibling step would represent a *promoted* (singleton) node, whose parent equals its child without hashing; honest provers omit such no-ops and the verifier rejects them. This makes the accepting path unique for a fixed `(leaf_hash, index, tree_size, root)`, closing prepend/insert malleability. (This concerns zero-*sibling* steps; the null-*valued* siblings of flat null promotion are unaffected.) Both properties are machine-checked as `inclusion_soundness` and `inclusion_proof_unique` — see [Formally Verified Properties](#formally-verified-properties-lean-4).

### The Null Constant & Authenticated Inactivity (Design A+)

The null constant $N_0$ represents an empty or inactive subtree. To stay hash-agile, it is defined per hasher rather than as a global static constant (the `Hasher::null` default, also exposed as the `null_digest` helper):

$$N_0 = \text{Hasher.hash}(\mathtt{"null"})$$

Under prefix-free hashing this definition makes one collision *public and trivial*: a genuine leaf whose payload is the literal 4-byte string `null` hashes to $N_0$. `neml` does not forbid that payload and does not assume the collision away. Instead, the design renders it inert:

*   **Activity is never inferred from digest null-ness.** Whether algorithm $X$ is active at position $p$ is read from the committed epoch timeline bound into the Combined Root (`committed_active_at`) — never by comparing a cell's digest to $N_0$. A verifier that infers inactivity from null-ness is unsound by construction, since the colliding leaf payload is perfectly legal.
*   **One-directional consistency check.** Verification asserts only `inactive ⇒ N₀`: a position the committed epochs mark inactive must hold the null constant in that algorithm's tree (`verify_inactivity_with_coupling`). It never constrains active cells, so no payload is ever forbidden. Read contrapositively, a non-null cell forces the committed timeline to mark the position active — a logger cannot commit a real leaf and later disown it via the epochs.
*   **Internal nodes cannot collide with $N_0$** except by a true hash collision: a node preimage concatenates at least two digests (≥ 2 × digest length), while `b"null"` is 4 bytes — the preimages differ in length.

### Formally Verified Properties (Lean 4)

The security core of NEML is machine-checked in the Lean 4 corpus at [`proofs/lean/`](../proofs/lean/) (see its README for a reviewer's guide). What is proved:

*   **Promotion semantics.** The evaluator mirroring `nary_mr` (singleton promotion, flat null promotion) is defined constructively; its evaluation equations are theorems, not axioms.
*   **Design A+.** `null_collision` (the leaf/null collision is constructible — the model is faithful to the shipped `null()`), `inferredActiveFromNull_unsound` (inferring activity from null-ness is unsound), `metaroot_binds_timeline` (two histories whose timelines disagree on activity anywhere cannot share a Combined Root unless the hash collides), and `real_cell_forces_committed_active` / `committed_inactive_is_null` (both directions of the consistency check).
*   **Canonical inclusion proofs.** `inclusion_soundness` (an accepting proof binds the leaf to its log *position*; depth is existential by design, since implicit promotion equates a promoted digest with its parent slot) and `inclusion_proof_unique` (at most one accepting canonical path per `(leaf_hash, index, tree_size, root)` statement, modulo an internal-node hash collision).
*   **K-ary construction and verifier soundness (any `k ≥ 2`).** [`Kary.lean`](../proofs/lean/EMLProof/Kary.lean) closes the V9 gap end-to-end. The shipped base-`k` carry schedule (`frontier_for_size` + `reduction_count`) is proved consistent (`frontier_append_consistent`); the frontier stack machine computes the perfect-subtree roots (`kary_bridge`, the k-ary generalization of the binary bridge lemma); and the **inclusion verifier itself** is modeled faithfully against `proof.rs` — the trailing steps pinned field-by-field to the concrete `inclusion_skeleton` (transcribed from `topology.rs`, with 11 `#guard` pins against its test vectors), zero-sibling steps rejected (canonical encoding), and the fold the null-promoting `nary_mr` rather than plain `node_hash`. `kary_completeness` shows honest proofs verify and `kary_inclusion_soundness` proves acceptance binds the leaf to log position `index` (depth existential).

The trust base is four declared axioms — an abstract digest type, its non-emptiness, the hash function, and digest serialization. Every theorem is `sorry`-free. The k-ary soundness adds **no axioms**: its two collision-style escape hatches (`NodeHashCollision`, `NullAmbiguity` — a node of ≥2 not-all-null children hashing to the null constant) appear only as explicit *hypotheses* on the theorems.

**Still unverified (honest scope):** the consistency and coupling verifiers; multi-algorithm/epoch interaction with the k-ary spine; and Rust-to-Lean transcription fidelity itself (mitigated, not eliminated, by the `#guard` pins). The full inventory of open formalization gaps is tracked in the [Lean README](../proofs/lean/README.md#7-future-formalization-work).

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

Inclusion proofs for a leaf nested inside a subtree must traverse **both** the subtree internals and the log-level tree. The proof path walks from the leaf up through the subtree (reconstructing the subtree root $R_i$), then continues through the log-level nodes (reconstructing the global root from $R_i$). Every step is linked via the hash function, forming an unbroken chain of commitments from the leaf to the global root. The verifier dynamically computes the boundary between subtree and log-level steps from the frontier structure — no separate verification mode is needed.

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
    // `null()` has a default implementation: hash(b"null").
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
