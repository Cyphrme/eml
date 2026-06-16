# EMLProof: Reviewer's Guide to Epoch Merkle Log Formalization

This directory contains the machine-checked mathematical proofs for Epoch Merkle Logs (EML),
formalized in Lean 4.

Rather than verifying a single concrete implementation, EMLProof formalizes a general model for
**hash-independent projective cryptography**, proving that a bottom-up incremental frontier
stack folds into a single root topologically identical to a top-down bisected RFC 9162 Merkle
tree.

---

## 1. Core Scientific & Cryptographic Novelties

A reviewer should focus on five primary mathematical demonstrations (A–E) that constitute the
core scientific contributions of this work; section F describes how the concrete and
generalized proof paths coexist:

### A. Hash-Independence via Structural Projection
Traditional Merkle proofs couple tree structure with cryptographic primitives. EMLProof
decouples them by proving its equivalences at the level of the inductive tree type
`MerkleTree α` (over a generic parameter `α`), independent of any hash function.
- The central equivalences (`bridge_lemma`, `generalized_bridge_lemma`) are equalities of
  *trees as data* — no hashing appears in their statements or proofs.
- Any concrete instantiation (e.g. `Digest` under hash `H`) is obtained by applying an
  evaluation function to both sides of the structural equality. Mechanically this is
  `congrArg`: `generic_projection_equivalence` records it once, for *any* evaluation function
  over *any* digest space.
- Consequently every structural theorem holds for every hash algorithm simultaneously, which
  is what makes the multi-algorithm construction possible.

### B. Generalized Shift-Reduce Duality
Instead of verifying only the concrete RFC 9162 / CTO equivalence, EMLProof proves a general
shift-reduce duality theorem for any append-consistent Merkle tree topology:
- **Abstract Interfaces**: Defines `SplitPolicy` (top-down partitioning) and `MergeSchedule`
  (bottom-up merges).
- **Append-Consistency**: A transition relation `AppendConsistent f s` asserting that the merge
  schedule `s` correctly transitions the forest sizes under policy `f` from $N$ to $N+1$, and that
  all intermediate splits match the policy.
- **Duality Theorem** (`generalized_bridge_lemma`): Proves that any `SplitPolicy` and
  `MergeSchedule` satisfying `AppendConsistent` are topologically equivalent.
- **Projective Pattern**: Because the duality is proved at the structural tree level, it
  projects to every concrete cryptographic digest space by evaluation (see A), for *any*
  append-consistent authenticated data structure.

### C. The Topological Bridge (RFC 9162 vs. MMR Peaks)
To remain backward-compatible with standard Certificate Transparency clients, EML must yield
a single root conforming to RFC 9162's top-down bisection (`largestPow2Lt`). However,
materializing this tree directly during appends requires $\mathcal{O}(n)$ hash operations.
- EML resolves this by executing a bottom-up MMR-like merge cascade internally ($\mathcal{O}(1)$
  amortized time).
- The **Bridge Lemma** (`bridge_lemma`) proves that folding this bottom-up stack is topologically
  isomorphic to RFC 9162's top-down bisection.
- **The Descent Condition**: Proving that the cascade merge always maintains descending
  power-of-two segments requires a modular arithmetic contradiction proof (`cto_trailing_geo`).
  It establishes that a degenerate stack layout would force a carry cascade larger than the
  one that actually occurred.

### D. Committed-Epoch Security (Design A+)
Multi-hash systems must authenticate *which* algorithm was active at *which* log positions. An
earlier iteration of this work claimed security from domain separation — inactive positions
held a domain-separated null constant, and activity was inferred from digest null-ness. The
formalization now models the shipped design (Design A+), which repudiates that inference:
- `null_collision` proves the leaf/null collision is *trivially constructible*: a genuine leaf
  whose payload is the 4-byte string `null` hashes to the null constant $N_0$. The model does
  not assume the collision away; A+ renders it inert.
- `inferredActiveFromNull_unsound` proves the legacy inference unsound: reading activity from
  digest null-ness misclassifies such a leaf as inactive.
- Activity is instead read from the **committed epoch timeline**, bound into the combined-root
  **metaroot** preimage. `metaroot_binds_timeline` proves non-equivocation: two histories with
  identical trees but timelines disagreeing on activity at any `(algorithm, position)` cannot
  share a combined root unless `H` collides. This binding is also the cross-algorithm
  non-interference statement: per-algorithm activity claims are individually committed and
  cannot be substituted under a fixed root.
- The verification-time consistency check `inactive ⇒ N₀` yields both remaining obligations:
  `real_cell_forces_committed_active` (a logger cannot commit a real leaf and later disown it
  via the epochs) and `committed_inactive_is_null` (no real leaf hides behind a retired claim).

### E. Canonical Inclusion Proofs (Soundness and Non-Malleability)
Under canonical proof encoding, zero-sibling ("promoted") steps are rejected, so every step of
an accepted inclusion proof strictly hashes (`not_canonical_of_promoted`).
- `inclusion_soundness` is the existential soundness statement: an accepting canonical proof
  exhibits a subtree root at the claimed log position that folds through the pinned log
  skeleton to the committed root. The claim binds the log *position*, never the depth —
  implicit promotion makes a promoted digest equal its parent slot (Cyphr SPEC §2.2.12).
- `inclusion_proof_unique` proves non-malleability: for a fixed statement there is at most one
  accepting canonical path, modulo an internal-node hash collision. The proof-shape pinning
  (path length and per-step positions) that the shared topology module
  (`neml/src/topology.rs`) derives from `(k, index, tree_size)` enters as premises; see
  [Future Formalization Work](#7-future-formalization-work).

### F. Coexistence of Concrete and Generalized Proof Paths
To optimize auditability and academic generality, EMLProof maintains two parallel proof paths:
- **The Concrete Path** ([Bridge.lean](EMLProof/Bridge.lean) /
  [Invariant.lean](EMLProof/Invariant.lean)):
  This path directly verifies the RFC 9162 / CTO equivalence. By avoiding template indirection,
  it remains highly readable and direct to audit.
- **The Generalized Path** ([Duality.lean](EMLProof/General/Duality.lean) /
  [Policy.lean](EMLProof/General/Policy.lean)):
  This path proves the shift-reduce duality for *any* append-consistent topology, showing the
  construction is a general combinatorial property.

Keeping these paths parallel separates the combinatorial duality theorem from the binary arithmetic
instantiation, avoiding unnecessary typeclass boilerplate in the production-grade CTO proofs.

---


## 2. Directed Reviewer's Code Map

To facilitate the formal review process, the following index maps the core proofs to their
locations in the source files:

- **[Policy.lean](EMLProof/General/Policy.lean)**:
  - `SplitPolicy` / `MergeSchedule` (L13 / L20): Abstract topology interface signatures.
  - `AppendConsistent` (L50–L55): Coherence condition mapping policy to schedule transitions.
- **[Duality.lean](EMLProof/General/Duality.lean)**:
  - `generalized_bridge_lemma` (L444–L447): General shift-reduce duality theorem.
- **[Instantiation.lean](EMLProof/General/Instantiation.lean)**:
  - `linear_split_policy` (L16): Linear split policy definition.
  - `linear_schedule_compatible` (L55): Proof of append-consistency for the linear policy.
  - `linear_bridge_lemma` (L66): Instantiated general bridge lemma.
- **[Tree.lean](EMLProof/Tree.lean)**:
  - `largestPow2Lt` (L51–L54): RFC 9162 top-down bisection boundary.
  - `cto` (L111–L114): Count Trailing Ones merge cascade count.
- **[Binary.lean](EMLProof/Binary.lean)**:
  - `cto_trailing_geo` (L441–L510): Descent condition (modular arithmetic bounds).
- **[Invariant.lean](EMLProof/Invariant.lean)**:
  - `stackInvariant` (L31–L37): Binomial forest loop invariant relation.
  - `appendToStack_invariant` (L82–L373): Preservation of stack invariant on append.
- **[Bridge.lean](EMLProof/Bridge.lean)**:
  - `stackRoot_segments_eq_mth` (L35–L153): Topological isomorphism inductive step.
  - `bridge_lemma` (L155–L166): Structural incremental-to-batch equivalence.
- **[Projection.lean](EMLProof/Projection.lean)**:
  - `generic_projection_equivalence`: Projection to any digest space (`congrArg` over a tree
    equality; no algebraic/homomorphism structure is involved).
  - `projection_equivalence`: EML Theorem 1 (Projection Equivalence).
  - The former "Temporal Binding" and "Algorithm Isolation" theorems were removed as vacuous
    (an axiom echo, and two independent copies of Projection Equivalence). Their intended
    security content is formalized in `NEML.lean`'s committed-epoch (Design A+) layer.
- **[NEML.lean](EMLProof/NEML.lean)** (security layer):
  - `eval` and its five evaluation equations (`eval_leaf`/`eval_empty`/`eval_singleton_node`/
    `eval_flat_null_node`/`eval_node_hash`): a real `def` with proved equations (formerly
    axioms); `eval_singleton`, `eval_flat_null_promotion`: promotion soundness.
  - `null_collision`: the faithful `leaf(b"null") = N₀` identity, now expressible and proved.
  - Design A+: `inferredActiveFromNull_unsound`, `metaroot_binds_timeline`,
    `real_cell_forces_committed_active`, `committed_inactive_is_null` — activity is read from
    the committed timeline bound into the combined-root metaroot, not from digest null-ness.
  - Canonical inclusion: `not_canonical_of_promoted`, `inclusion_soundness`, and
    `inclusion_proof_unique` (non-malleability) — all fully proved. Uniqueness holds modulo
    `NodeHashCollision` and takes the proof-shape pinning (`hlen`/`hpos`) as premises,
    mirroring the guarantees of `neml/src/topology.rs`
    (see [Future Formalization Work](#7-future-formalization-work)).

### 2.1. How to Audit and Verify Axioms (TCB)
To verify which axioms and `sorry` placeholders the theorems depend on, a reviewer can inspect
the Trusted Computing Base (TCB) using Lean's `#print axioms` command:
1. Append the following diagnostics to the end of [NEML.lean](EMLProof/NEML.lean):
   ```lean
   #print axioms NEML.projection_equivalence
   #print axioms NEML.eval_flat_null_promotion
   #print axioms NEML.metaroot_binds_timeline
   #print axioms NEML.inclusion_proof_unique
   ```
2. Build the project. The compiler output will display the exact axioms utilized.
3. The NEML/Projection layer declares **exactly four** domain constants:
   `Digest`, `Digest.nonempty`, `H`, and `digestToBytes` (plus Lean built-ins `propext`,
   `Classical.choice`, `Quot.sound`). This corrects the earlier claim of five — the
   `domain_separation` axiom and the NEML `numsSeed`/`xof`/`eval`-cluster axioms (thirteen in
   total before) were removed. Every theorem in the corpus is `sorry`-free: no `#print axioms`
   output contains `sorryAx`.


### 2.2. Paper-to-Formalization Dictionary
For convenience, this table maps the formal names used in the accompanying paper to their
respective Lean symbols in the source code:

| Paper Entity | Lean Symbol Link | Description |
| :--- | :--- | :--- |
| **Definition 2** | [mth](EMLProof/Tree.lean#L92) | Batch Merkle Tree Hash |
| **Definition 3** | [cto](EMLProof/Tree.lean#L112) | Count Trailing Ones count |
| **Theorem 1** | [bridge_lemma](EMLProof/Bridge.lean#L155) | Structural Bridge Lemma |
| **Theorem 2** | [projection_equivalence](EMLProof/Projection.lean) | Projection Equivalence |
| **Temporal Binding** | [metaroot_binds_timeline](EMLProof/NEML.lean), [real_cell_forces_committed_active](EMLProof/NEML.lean) | Inactivity authenticated by the committed epoch timeline (Design A+); supersedes the removed vacuous `temporal_binding` |
| **Algorithm Isolation** | [metaroot_binds_timeline](EMLProof/NEML.lean) | Per-algorithm commitments bound into the metaroot; supersedes the removed vacuous `algorithm_isolation` |
| **Inclusion Soundness** | [inclusion_soundness](EMLProof/NEML.lean) | Accepting canonical proof commits the leaf at the claimed log position (depth existential) |
| **Non-Malleability** | [inclusion_proof_unique](EMLProof/NEML.lean) | At most one accepting canonical path per statement, modulo internal-node hash collision |
| **Theorem 5** | [generalized_bridge_lemma](EMLProof/General/Duality.lean#L444) | Generalized Bridge Lemma |
| **K-ary Carry Schedule** | [frontier_append_consistent](EMLProof/Kary.lean) | The shipped `frontier_for_size` + `reduction_count` schedule is `AppendConsistent` (base-`k`, any `k ≥ 2`) |
| **K-ary Bridge** | [kary_bridge](EMLProof/Kary.lean) | The frontier stack machine computes the perfect-subtree roots of the frontier decomposition (k-ary generalization of `bridge_lemma`) |
| **K-ary Completeness** | [kary_completeness](EMLProof/Kary.lean) | Honest inclusion proofs verify against the null-promoting fold and concrete skeleton |
| **K-ary Inclusion Soundness** | [kary_inclusion_soundness](EMLProof/Kary.lean) | Accepting proof commits the leaf at log position `index` (depth existential), modulo two explicit hash assumptions |
| **K-ary Consistency Soundness** | [consistency_soundness](EMLProof/KaryConsistency.lean) | Accepting consistency proof against the honest current root forces the reconstructed `oldRoot` to the genuine size-`oldSize` prefix root, modulo two explicit hash assumptions |
| **K-ary Append-Only** | [consistency_append_only](EMLProof/KaryConsistency.lean) | Accepting a proof between two honest roots forces `oldCells <+: newCells` at the data level |
| **K-ary Consistency Completeness** | [consistency_completeness](EMLProof/KaryConsistency.lean) | Honest consistency proofs verify, reconstructing the genuine prefix and current roots (non-vacuity witness) |


---

## 3. Build & Verification Instructions

The Lean 4 proof environment is managed via a Nix shell. Run the following command at the
directory root to check all proofs:

```bash
nix-shell --run "lake build"
```

A successful compile outputs `Build completed successfully` with zero warnings and zero errors.

---

## 4. Semantic Correspondence with Rust Code

To verify that the formalized state machine matches the production implementation:
1. **CTO Cascade**: The Rust implementation in `src/log.rs` (`count_trailing_ones`) uses the
   constant-time bitwise instruction `(!n).trailing_zeros()`, which matches the recursive `cto`
   definition in `Tree.lean`.
2. **Stack Traversal**: The Rust stack is represented as a vector with the top at the end, and the
   root is folded right-to-left. The Lean stack represents the top at the head of the list and
   folds left-to-right. Both expand to the same parent node evaluation order:
   `node(left_sibling, right_accumulator)`.
3. **Null Prefix Peaks**: The MMR peaks initialized during algorithm activation in `src/log.rs`
   (`null_prefix_peaks`) match `null_prefix_peaks` in the formal model.
4. **NEML Security Layer**: The committed-epoch model in `NEML.lean` mirrors the production
   NEML crate: `nullPreimage`/`nullDigest` match `neml/src/hasher.rs`
   (`null() = hash(b"null")`); `committedActiveAt` matches `committed_active_at` in
   `neml/src/proof.rs`; the metaroot preimage models `combined_root_preimage`
   (`neml/src/proof.rs`) and `combined_root_at` (`neml/src/tree.rs`); the `inactive ⇒ N₀`
   consistency check (`InactiveImpliesNull`) models `verify_audit_payload`
   (`neml/src/tree.rs`); the proof-shape pinning assumed by `inclusion_proof_unique`
   corresponds to the shared topology module `neml/src/topology.rs` (`frontier_for_size`).

---

## 5. Formal Red Team Audit & Vulnerability Analysis

To stress-test the formalization against potential mathematical or semantic exploits, we present
the findings of our formal red-team audit:

### A. Axiom Minimality and Soundness
- The codebase relies on exactly four structural/domain axioms declared in `Projection.lean`: the
  existence of `Digest`, its non-emptiness, a hashing operator `H`, and a digest serializer
  `digestToBytes`. (This corrects an earlier claim of five: the `domain_separation` axiom and the
  NEML `numsSeed`/`xof`/`eval`-cluster axioms — thirteen in total before — were removed.)
- We assume no structural algebraic properties of `H` (such as associativity or commutativity). The
  proof is purely combinatorial and arithmetic.
- The model does **not** assume the null constant is unreachable. The faithful definition makes the
  `leaf(b"null") = N₀` collision expressible (`null_collision`); soundness comes instead from
  reading activity off the committed epoch timeline bound into the metaroot (Design A+), so the
  collision is inert rather than assumed away.

### B. Generalized Topology Robustness
- **Fallback Logic**: If the policy function `f` is invalid (e.g., returns 0 or a split $\ge n$),
  `generalized_mth` falls back to returning `MerkleTree.empty`. Because all theorems are guarded by
  `Fact (ValidSplitPolicy f)` (which guarantees $0 < f(n) < n$), this fallback branch is proven
  unreachable.
- **Underflow Protection**: If a merge schedule `s n` exceeds the stack height, the machine
  handles underflow safely by returning the remaining stack untouched, preventing empty list panics.
- **Degenerate Structures**: The framework successfully admits trivial policies (like the linear
  split policy with 0 merges proved in [Instantiation.lean](EMLProof/General/Instantiation.lean))
  showing that the shift-reduce duality is a general property of all append-consistent trees.

### C. Lean-to-Rust Semantic Gaps
- **CTO Cascade**: Rust uses the constant-time bitwise instruction `(!n).trailing_zeros()`, while
  Lean uses the recursive function `cto`. These are equivalent for all $n < 2^{64}$.
- **Stack Fold Order**: Lean folds from top to bottom (left-to-right), whereas Rust vectors fold
  right-to-left. Both expand to the identical parent node evaluation order:
  `node(left_sibling, right_accumulator)`.
- **Epoch Boundaries**: The finite epoch stops in the model do not restrict the proof since
  equivalence holds for any static projection evaluation at size $N$.

### D. Invalidation Vectors
- **Boundary Cases**: Zero-length and single-length boundary cases are closed by explicit guards in
  `largestPow2Lt` and structural checks in `mth`.
- **Activity Forgeries**: The model does *not* rely on domain separation at inactive positions —
  the leaf/null collision is trivially constructible (`null_collision`). Forging an activity
  status under a fixed combined root instead requires an `H` collision on the metaroot
  preimage (`metaroot_binds_timeline`), and hiding a real leaf behind an inactive claim is
  excluded by the `inactive ⇒ N₀` check (`committed_inactive_is_null`).
- **Proof Malleability**: Padding an inclusion proof with promoted (zero-sibling) steps is
  rejected outright under canonical encoding (`not_canonical_of_promoted`); within canonical
  encoding, `inclusion_proof_unique` leaves an internal-node hash collision as the only
  rerouting vector.
- **Resumption Divergence**: Stack reconstruction from stored nodes (`reconstruct_frontier`) is
  guaranteed to equal continuous appends because of the proven uniqueness of the descending
  binomial stack partition.

---

## 6. K-ary construction and verifier soundness (V9)

[Kary.lean](EMLProof/Kary.lean) closes the V9 gap end-to-end for arbitrary arity
`k ≥ 2`. **Now proven** (`sorry`-free):

- the **k-ary construction** and the **shipped base-`k` carry schedule**
  (`frontier_for_size` + `reduction_count`), via `frontier_append_consistent`
  and `kary_bridge` — previously proven for no real policy (only the degenerate
  `linear_split_policy`, and only for binary nodes);
- the **inclusion verifier**, modeled faithfully against `proof.rs`: the trailing
  steps are pinned field-by-field to the concrete `inclusionSkeleton` (the single
  topology authority, transcribed from `topology.rs`), zero-sibling (promoted)
  steps are rejected (canonical encoding), and the fold is the **null-promoting**
  `naryMr`, not plain `nodeHash`. `kary_completeness` shows honest proofs verify
  (the non-vacuity witness) and `kary_inclusion_soundness` shows acceptance binds
  the leaf to log position `index` (existential in depth, per Cyphr SPEC §2.2.12).
- the **consistency verifier**, modeled faithfully against
  `reconstruct_consistency_roots` (`proof.rs`): a single shared path anchored at
  `start_hash` reconstructs both the old-size and new-size roots, with the
  coordinate→digest map (`consistencyMap`) read back at every old-frontier
  coordinate. `consistency_completeness` shows honest proofs verify (non-vacuity),
  `consistency_soundness` shows acceptance against the honest current root forces
  the reconstructed `oldRoot` to the genuine prefix root, and
  `consistency_append_only` lifts that to the data-level append-only relation
  `oldCells <+: newCells` — all modulo the same two explicit hash assumptions.

The transcription is pinned to `topology.rs` test vectors by 11 `#guard` checks,
so definitional drift breaks the build rather than passing silently.

**Trust base unchanged:** the four structural axioms below still bound the TCB.
The k-ary soundness adds **no axioms** — its two collision-style escape hatches
(`NodeHashCollision`, `NullAmbiguity`) appear as explicit *hypotheses* on the
theorems, not as axioms.

**Still UNVERIFIED** (honest scope): the coupling verifier;
multi-algorithm/epoch interaction with the k-ary spine; and Rust-to-Lean
transcription fidelity itself (mitigated, not eliminated, by the `#guard` pins).

---

## 7. Future Formalization Work

The realignment left the following gaps open, each flagged at its site in the source:

1. **Legacy `SkeletonValid` premise.** The corpus-level `inclusion_proof_unique`
   still takes the proof-shape pinning as premises (`hlen`, `hpos`) over the
   abstract `SkeletonValid`. The concrete topology is now ported in
   [Kary.lean](EMLProof/Kary.lean) (`inclusionSkeleton`), and
   `kary_inclusion_soundness` proves soundness against it directly; folding the
   legacy `NEML.lean` uniqueness statement onto the concrete skeleton (or
   retiring it in favor of the k-ary version) would discharge those premises.
2. **Legacy verifier transcription.** `reconstructPathRoot`, `verifyInclusion`, and the
   `partial def` topology helpers in `NEML.lean` are a direct transcription of the
   pre-canonical Rust verifier, retained for reference; no theorem depends on them. They
   should either be connected to the canonical model (`foldCanonical`/`Accepts`) or removed
   once the topology port lands.
3. **Vestigial digest-length parameter.** The `L : Nat` parameter threaded through `eval` and
   `nullDigest` is vestigial — the shipped null constant is length-independent — and could be
   dropped in a later cleanup.

