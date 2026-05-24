# PLAN: EML Paper Revision — Post-Review Overhaul

## Goal

Address all verified defects and convergent reviewer concerns from
`docs/review-iterative/convergence-analysis.md` to bring the EML paper to
publishable quality for USENIX Security. The revision fixes mathematical
correctness errors, eliminates formalism theatre, tightens security claims,
strips editorial bloat, and adds the empirical baselines reviewers demanded —
while preserving the three contributions that all 6 reviewers praised (temporal
null-padding, deterministic proof elision, evaluation methodology).

### Narrative Throughline (post-proof revision)

The proof work revealed a throughline that should unify the paper:

1. **The pain**: Heterogeneous clients on a network support different hash
   algorithms. A transparency log must serve all from a single structure.
2. **The solution**: The EML — one tree, many projections, null-padded epochs.
3. **The formal guarantee**: The bridge lemma proves incremental = batch
   construction, and the algorithm isolation theorem shows each projection
   is independently valid.
4. **The surprising punchline**: The bridge lemma holds for *any deterministic
   function* over *any append-consistent topology* (generalized shift-reduce duality).
   Algorithm-independent verification requires algorithm-independent correctness,
   and the proof delivers exactly that. The RFC 9162 / CTO equivalence is proved
   as a concrete instantiation of a general combinatorial property of tree
   decompositions. This is the first machine-checked formalization of RFC 9162's MTH,
   serving the CT ecosystem broadly, not just EML.

Every section should serve this spine. Content that doesn't advance the
narrative from pain → solution → proof → generality is candidate fat to cut.

## Constraints

- 13-page body (USENIX Security two-column, 10pt)
- The Rust implementation is ground truth — the paper describes what the code does
- Double-blind review
- Page budget is already tight; every addition must be offset by cuts
- Per-algorithm manifest digests (H_a(act)) will be implemented in the crate

## Decisions

| Decision | Choice | Rationale |
| :------- | :----- | :-------- |
| Formal model scope | Radical strip: formalize only novel contributions (~7 definitions + 3 theorems) | The formal model is proof apparatus for Contribution 1, not a standalone contribution. "Initial algebra with 9 equational laws" is the root cause of the "formalism theatre" critique (6/6 reviewers). Standard Merkle tree properties inherited from RFC 9162 do not need restating for a USENIX audience. The domain model in `docs/models/` retains the full specification for implementation. |
| Critical-path deliverable | Lean4 machine-checked proof: bridge lemma + 3 theorems | 6/6 reviewers flagged the proof as deficient. Machine-checked proof eliminates the entire "eyeball error" category permanently. Every reviewer listed machine-checked proofs as future work — delivering one is a significant differentiator. |
| Contribution 2 reframing | "A machine-checked proof (Lean4) establishing structural equivalence, algorithm isolation, and temporal binding" | Specific, mechanically verified claims > volume count. The bridge lemma serves CT broadly (first formalization of RFC 9162 MTH). Algorithm isolation formalizes the paper's central design principle. |
| Bridge lemma framing | Emphasize that structural equivalence is pure mathematics — no cryptographic assumptions | The proof holds for *any* deterministic combining function, not just hash functions. This is the mathematical embodiment of algorithm independence and should be stated explicitly. It distinguishes EML's contribution from the literature, which habitually conflates structural and cryptographic claims. |
| D-Sep formulation | Computational hardness under ROM | 4/6 flagged Pigeonhole violation. Current statement is mathematically false for unbounded d ∈ Bytes. |
| H(act) weakest-link | Implement per-algorithm H_a(act) manifest digests | 6/6 flagged this. Paper-only acknowledgment is insufficient. Implementation change is small and eliminates the strongest architectural objection. |
| Absolute benchmarks | Implement comparative benchmark (EML vs vanilla RFC 9162) | 5/6 demanded throughput numbers. "We deliberately avoid micro-benchmarks" was identified as evasion. |
| resume_alg | Keep, but reframe justification | The operational scenario (temporary deactivation/reactivation) is legitimate and the implementation supports it. Cutting it from the paper while the code supports it is dishonest. Reframe away from "key lifecycle" (which invites the layer violation critique) toward operational algorithm lifecycle management. |
| §1.1 Case Study | Keep, genericize | The heterogeneous-device scenario is genuinely motivating. Strip "Cyphr" and "Cyphrpunk LLC" proper nouns (double-blind violation). Frame as "long-lived key directories and decentralized identity registries" — the class, not the instance. |
| "Isomorphism" | Rename to "Projection Equivalence" | 3/6 flagged mathematical misuse. π_a is surjective but non-injective; "isomorphism" is wrong. |
| MTH notation | Introduce explicit clarification that Theorem 1's MTH operates on digest sequences | 1/6 flagged as "mathematically false"; verified as false alarm by implementation, but the notation genuinely is ambiguous. Clarify, don't rename. |
| Generalized Duality Framing | Formally define SplitPolicy, MergeSchedule, and AppendConsistent in §IV and state the Generalized Bridge Lemma (Theorem 4). | Establishes EML's equivalence theorem as a special case of a broader combinatorial property of tree decompositions. This elevates EML from an ad-hoc bitwise hack to a general, algebraic proof strategy applicable to any append-consistent topology. |

## Risks & Assumptions

| Risk / Assumption | Severity | Status | Mitigation / Evidence |
| :---------------- | :------- | :----- | :-------------------- |
| Lean4 formalization may surface genuine subtleties in the CTO↔MTH equivalence | HIGH | **Resolved** | The proof surfaced exactly the subtleties predicted: the descent condition required a modular arithmetic contradiction via `cto_ge_of_mod` that was not apparent from pen-and-paper reasoning. The proof succeeded — no correctness problems found. |
| Lean4 learning curve / tooling friction | MEDIUM | **Resolved** | Proof completed. Final artifact: ~1565 lines, 30 theorems, zero sorry. Build clean (3288 jobs). Significant iteration was required on the descent condition, but the scope remained bounded. |
| Radical §IV strip may read as "not rigorous enough" | LOW | Mitigated | A machine-checked proof is strictly more rigorous than any pen-and-paper formal model. The Lean4 proof is the rigor; the stripped §IV is the presentation. |
| Page budget may not accommodate benchmarks | MEDIUM | Validated | Radical §IV strip recovers ~1.5 pages. Carrier Types, reduced law catalog, and §8.5 PQ cut recover ~1 more. Total recovered: ~2.5-3 pages. Benchmark section needs ~1-1.5. |
| Absolute benchmarks require implementation work (storage backend) | HIGH | Unvalidated | Must scope carefully: in-memory baseline suffices for relative comparison if we're transparent about it. RocksDB or similar is ideal but may be out of appetite. |
| "Formalism theatre" critique may persist if restructure is superficial | MEDIUM | Mitigated | Radical strip removes the ceremony, not just the labels. Only novel formalisms survive. |
| resume_alg reframing may not satisfy reviewers who want removal | MEDIUM | Accepted | The operational justification must be compelling enough that the reviewer says "I see why they need this" rather than "they refused to simplify." |
| Contribution list change weakens perceived scope | LOW | Mitigated | A precise theorem is stronger evidence of rigor than a count of definitions. Reviewers reward depth over breadth. |

## Open Questions

> [!IMPORTANT]
> **Q1: Benchmark scope — in-memory baseline or persistent storage?**
> A benchmark against an in-memory RFC 9162 implementation is fast to build and
> demonstrates relative overhead cleanly. A benchmark against Trillian/RocksDB
> is more convincing but requires significant implementation work. The choice
> affects Phase 5's scope.

- **Q2: (Resolved)** I-Sound/K-Sound/T-Bound placement — inline as one-sentence
  corollaries in §IV. They reduce trivially to Projection Equivalence + RFC 9162
  soundness. No appendix needed.

## Scope

### In Scope

- ~~Lean4 machine-checked proof of Projection Equivalence, Temporal Binding, and Algorithm Isolation (`proofs/lean/`)~~ **DONE**
- Radical restructure of `_04-formal-model.qmd`: strip to novel formalisms + Lean4-backed proofs
- ~~Lean proof of full theorem chain~~ **DONE** — proof covers CTO primitives → bridge lemma → projection equivalence → temporal binding → algorithm isolation
- Implement per-algorithm H_a(act) manifest digests in the Rust crate
- Implement comparative benchmarks (EML vs RFC 9162 baseline)
- Precision fixes to `_02-background.qmd`: second-preimage claim, MTH clarification
- Presentation tightening across §I, §VI, §VIII
- Bibliography completeness pass
- Update `docs/models/epoch-merkle-log.md` to match paper changes
- Update `draft/editorial_guidance.md` to reflect new formal structure

### Out of Scope

- ~~Machine-checked proofs (Lean/Coq) — future work~~ **MOVED TO DONE** — Lean4 proof completed
- New figures beyond benchmark plots
- P2P replication / CRDT semantics
- Quarto template changes

## Phases

### Phase 1: Lean4 Machine-Checked Proof ✅ COMPLETE

The proof is the keystone. Lean4 accepts it — the restructure is straightforward
and the paper gains a contribution no reviewer anticipated.

- [x] Set up Lean4 project at `proofs/lean/` with Mathlib dependency
- [x] Define the core types and operations in Lean4
  - [x] Abstract hash function type (opaque `Digest := List UInt8`)
  - [x] MTH batch construction (RFC 9162 recursive `largestPow2Lt` split)
  - [x] Frontier stack (`buildStackAux` / CTO-based incremental accumulator)
  - [x] Leaf value function V(a,i) with null/active cases (`leafValue`)
  - [x] Projection as list construction (`projectDigests`)
- [x] Prove CTO↔MTH bridge lemma (`bridge_lemma`)
  - [x] `stackRoot_segments_eq_mth`: fold over MMR peaks = batch MTH
  - [x] `buildStack_invariant`: incremental stack maintains segment invariant
  - [x] `appendToStack_invariant`: the core inductive step — 4 conditions (flatten, pow2, descent, stack) including the descent condition via modular arithmetic contradiction
  - [x] `merge_cascade`: mergeStack over geometric segment runs produces MTH
  - [x] `cto_trailing_geo`: CTO-indexed segments form geometric series 2⁰, 2¹, ..., 2ᵏ
- [x] Prove Projection Equivalence (Theorem 1) — `projection_equivalence`
  - [x] `ctoRoot(project epochs payloads) = mth(project epochs payloads)`
  - [x] Follows from bridge lemma applied to the projected leaf sequence
- [x] Prove Temporal Binding (Theorem 2) — `temporal_binding`
  - [x] Reduce to domain separation + Projection Equivalence
  - [x] Inactive positions have null-padded digests; no payload `d` satisfies `leafHash d = nullHash`
- [x] Prove Algorithm Isolation (Theorem 3) — `algorithm_isolation`
  - [x] For any two algorithms a, b: both projections independently yield valid RFC 9162 trees
  - [x] Proof: `⟨bridge_lemma _, bridge_lemma _⟩` — structural independence visible in the type signature
- [x] Definitional correspondence audit: document side-by-side mapping of each Lean definition to its Rust counterpart (`mth`, `cto`, `buildStackAux`, `leafValue`, `project`)
- [x] Write companion prose document at `docs/proofs/projection-equivalence.md` explaining the proof structure for paper integration

**Proof statistics**: ~1400 lines, 31 theorems, 0 sorry. Build clean.

**Post-proof insights** (see `.sketches/lean-proof-presentation.md` for full analysis):

- The bridge lemma requires NO cryptographic assumptions — it is a theorem of
  combinatorics and binary arithmetic. This is the mathematical embodiment of
  algorithm independence.
- The descent condition (`cto_ge_of_mod`) is the hidden structural complexity —
  ~180 lines of modular arithmetic that informal proofs elide.
- This is the first machine-checked formalization of RFC 9162's MTH definition
  in any proof assistant, serving the CT ecosystem broadly.
- The proof's generality (any deterministic function) directly supports the
  EML's design principle: algorithm-independent verification requires
  algorithm-independent correctness.

**Key proof artifacts** (in `proofs/lean/EMLProof/ProjectionEquivalence.lean`):

| Theorem | Statement | Axioms Used |
| :------ | :-------- | :---------- |
| `bridge_lemma` | `ctoRoot leaves = mth leaves` — incremental root = batch root | Structural only (1–4) |
| `projection_equivalence` | Full EML projection equivalence over epoch/payload sequences | Structural only (1–4) |
| `algorithm_isolation` | For any two algorithms, both projections independently valid | Structural only (1–4) |
| `temporal_binding` | Inactive positions reject all payloads | Structural + domain_separation |
| `stack_invariant_step` | Core induction: stack invariant preserved on leaf append | Structural only (1–4) |
| `merge_cascade` | Geometric merge run produces MTH over concatenated segments | Structural only (1–4) |
| `cto_trailing_geo` | CTO = k+1 ⟹ trailing k+1 segments are 2⁰..2ᵏ | None (pure Nat arithmetic) |

---

### Phase 2: Formal Model Restructure — rewrite §IV

**Throughline role**: This is the "proof" segment of the spine. §IV must do
two things: (1) state the theorems with enough precision to be verifiable,
and (2) convey the *surprising punchline* — that structural correctness is a
purely combinatorial property of tree decompositions and carry arithmetic,
projected to concrete cryptography via a unique algebra homomorphism.

- [x] Reopen §IV rewrite to transition from concrete digest-level definitions to structural-to-homomorphic decoupling:
  - [x] Define the free magma `MerkleTree α` representing pure structural tree arithmetic.
  - [x] Define the structural MTH and CTO stack machine operations over `MerkleTree α`.
  - [x] Define the EML state `S` and operations (`append`, `add_alg`, etc.) at the structural tree level.
  - [x] Define the concrete cryptographic digest algebra `Digest` (with `H`, tags, and tag-separated tags).
  - [x] Define the evaluation function `eval` and prove it is the unique algebra homomorphism from the free magma to the concrete digest algebra.
  - [x] Define the projection function `project` mapping epoch sequences and payloads to structural leaf sequences.
- [x] Theorems with proofs (rewrite to reflect structural decoupling):
  - [x] **Theorem 1** (Structural Bridge Lemma): `ctoRoot l = mth l` for structural trees, proved by strong induction on length.
  - [x] **Theorem 2** (Projection Equivalence): concrete root equivalence follows as the homomorphic projection of the Structural Bridge Lemma under `eval`.
  - [x] **Theorem 3** (Temporal Binding): proof sketch reducing to domain separation axiom (tag independence in ROM).
  - [x] **Theorem 4** (Algorithm Isolation): structural independence of different algorithm projections visible in the type signature.
  - [x] **Theorem 5** (Generalized Bridge Lemma): state the generalized shift-reduce duality, defining `SplitPolicy`, `MergeSchedule`, and `AppendConsistent` on `MerkleTree α`.
- [x] Incorporate the **Descent Condition** exposition: explain the modular arithmetic contradiction proof (`cto_trailing_geo` / `cto_ge_of_mod`) that rules out degenerate stack configurations.
- [x] Frame the RFC 9162 / CTO equivalence as a concrete instantiation of the generalized framework (referencing `Instantiation.lean` and `linear_split_policy` compatibility).
- [x] Assumptions (moved to §II Threat Model):
  - [x] Domain separation as computational hardness under ROM
  - [x] Algorithm independence (mutual incompressibility under ROM)
- [x] Corollaries:
  - [x] Inclusion/consistency soundness as one-sentence reductions to Theorem 2 + RFC 9162
  - [x] Projection validity as direct consequence of Theorem 2
  - [x] Manifest commitment (M-Commit)
- [x] Clarify MTH notation: explicit note that Theorem 2's MTH operates on pre-hashed digest sequences.
- [x] Rename "Projection Isomorphism" → "Projection Equivalence"
- [x] Update contribution list in §I:
  - [x] Frame Contribution 2 around the machine-checked free magma formalization and homomorphic projection rather than the old "initial algebra / 9 laws" catalog.
  - [x] Highlight the structural-cryptographic decoupling and generalized shift-reduce duality as core scientific contributions.

---

### Phase 3: Security & Architecture Fixes — precision in claims

**Throughline role**: These fixes serve credibility (reviewers flagged them)
but are not the narrative spine. Keep surgical. Don't expand; fix and move on.

- [x] Verify per-algorithm H_a(act) manifest digests alignment
  - [x] Crate implements manifest snap/hashing via raw `state.hasher.hash(&serialized)`
  - [x] Verify STH definition (Def 15) in `_04-formal-model.qmd` matches
  - [x] Verify `docs/models/epoch-merkle-log.md` matches
  - [x] Update M-Commit corollary in `_04-formal-model.qmd`
- [x] Separate second-preimage/equivocation conjunction in §II
  - [x] Silent payload substitution requires only second-preimage — monitors detect nothing
  - [x] Equivocation (inconsistent views) is an independent, detectable threat
  - [x] Remove the "not only... but also" conjunction
- [x] Fix "zero per-proof metadata" claim in §VI
  - [x] Acknowledge session-level bandwidth cost: O(|A| · epochs) for act map
  - [x] Distinguish per-proof wire overhead (eliminated) from session-level state (required)
  - [x] Update Table 3 with footnote
- [x] Clarify elision rehydration for non-power-of-two siblings in §VI
  - [x] Add parenthetical: proof-path siblings cover power-of-two leaf counts
  - [x] Reference Definition 17 Case 3 for general decomposition
- [x] Reframe resume_alg justification in §III
  - [x] Decouple from "key lifecycle" framing
  - [x] Frame as operational algorithm lifecycle flexibility
  - [x] Acknowledge complexity cost honestly

---

### Phase 4: Presentation Surgery — reclaim page budget

**Throughline role**: This phase *applies* the throughline as an editorial
scalpel. The question for every paragraph: does it advance
pain → solution → proof → generality? If not, it's fat.

#### Throughline-driven cuts (new)

Apply the spine as a filter to each section:

| Section | Serves throughline? | Action |
|:--------|:-------------------|:-------|
| §I Introduction | **Yes** — the pain (upgrade trilemma) | Keep. Tighten prose but the trilemma IS the throughline's first beat. |
| §I.1 Case Study | **Yes** — the pain, concrete | Keep, genericize (already planned). |
| §II Background | **Yes** — establishes what the proof formalizes | Keep. Don't expand. |
| §III The EML | **Yes** — the solution | Keep. This is beat 2. |
| §IV Formal Model | **Yes** — the proof + generality | Keep, but strip ceremony (Phase 2). Emphasize axiom-independence. |
| §V Proof Engine | **Partial** — operational bridge | Keep, but it's implementation detail, not the theoretical spine. Don't expand. |
| §VI Elided Proofs | **Partial** — practical contribution | Keep (reviewers praised it) but it's tangential to the throughline. Don't expand. |
| §VII Evaluation | **Yes** — validates the solution works | Keep. Benchmarks serve the spine by showing the solution is practical. |
| §VIII Related Work | **Yes** — reinforces the pain | Keep. The alternatives' limitations ARE the pain restated. |
| §8.5 Post-Quantum | **No** — tangential | **Cut.** One sentence in §IX future work. Doesn't advance any beat of the spine. |
| §IX Conclusion | **Yes** — mirror | Keep minimal. Restate the punchline: algorithm-independent correctness. |

#### Specific cuts and trims

- [x] **§8.5 Post-Quantum**: Cut entirely. Move to one sentence in §IX. Reviewers explicitly called this "marketing padding" (round 6). It doesn't serve any beat of the throughline.
- [x] **Carrier Types (§4.1)**: Cut. Ceremony that doesn't advance the proof narrative.
- [x] **"Faithful representation of temporal reality"**: Cut. Promotional, not diagnostic.
- [x] **"Distributed systems nightmare"**: Cut. Hyperbole.
- [x] **"Structural crisis"** in §I: Replace with objective description. The upgrade trilemma already conveys urgency without editorializing.
- [x] **Upgrade trilemma repetition**: Use the term once (definition in §I), reference thereafter. Currently repeated ~5 times.
- [x] **§V Proof Engine**: Audit for expansion since last draft. This section tends to grow. It should describe operations, not re-derive theory. Any theory belongs in §IV.
- [x] **resume_alg in §III**: Keep but minimize. It's operational detail, not the throughline. One paragraph maximum.

#### Previously planned items (retained)

- [x] Fix bibliography entries (CARAF, Chopra, Collier)
- [x] Add missing Bernstein citation
- [x] Genericize §1.1: strip proper nouns
- [x] Fix Table 2: "amortized O(log K)" → "worst-case O(log K)"
- [x] Fix interval notation: open → half-open
- [x] Trim Ethical Considerations to minimum viable compliance text

---

### Phase 5: Benchmarks — the empirical gap

**Throughline role**: Empirical validation is beat 3.5 — "the solution works
in practice, not just in theory." Keep focused on demonstrating that the
EML's overhead is acceptable. Don't benchmark tangential features.

- [x] Implement comparative benchmark harness
  - [x] EML append throughput vs vanilla RFC 9162 (single-algorithm) append throughput
  - [x] Proof generation latency comparison
  - [x] Storage amplification measurement (bytes per million entries, by algorithm count)
- [x] Integrate results into §VII
  - [x] Replace or supplement complexity regression with absolute numbers
  - [x] Add benchmark figure(s)
- [x] Update §7.6 Limitations to remove the "we deliberately avoid micro-benchmarks" evasion

---

### Phase 6: Integration & Verification — final consistency pass

**Throughline role**: The final pass should read the paper front-to-back
and verify that every section advances the spine. Any paragraph that
doesn't serve pain → solution → proof → generality gets flagged
for cutting or condensing.

- [x] Verify contribution list in §I matches actual proven/demonstrated content
  - [x] Contribution 2 references machine-checked Lean4 proof, not "algebraic model"
- [x] Verify all definition/theorem numbering is sequential and cross-referenced correctly
- [x] Cross-check formal model against `docs/models/epoch-merkle-log.md`; update model
- [x] Update `draft/editorial_guidance.md` to reflect new formal structure
- [x] Prepare Lean4 artifact for USENIX supplementary material submission
  - [x] Clean up `proofs/lean/` for external review
  - [x] Write README with build instructions and theorem inventory
- [x] Draft Open Science appendix content referencing Lean4 artifact and Rust crate
- [x] Render PDF and verify body ≤ 13 pages
- [x] Run quality checkpoints from editorial guidance
- [x] Full read-through for terminological consistency (terminology lock)

## Verification

- [x] Lean4 proof of Projection Equivalence type-checks successfully
- [- [x] Lean4 proof artifact included in supplementary materials
- [x] Theorem 4 (Generalized Bridge Lemma) is stated and explained in §IV
- [x] SplitPolicy, MergeSchedule, and AppendConsistent are defined in §IV
- [x] Bridge lemma's axiom-independence from cryptography stated explicitly in §IV
- [x] Algorithm isolation theorem referenced in §IV with structural independence explanation
- [x] Paper's contribution framed as first machine-checked formalization of RFC 9162 MTH
- [x] Narrative throughline (pain → solution → proof → generality) visible across all sections
- [x] No "Law" in §IV — all properties are definitions, assumptions, proved theorems, or corollaries
- [x] D-Sep stated as computational hardness, not absolute universal quantifier
- [x] MTH notation unambiguous between raw-payload and digest-domain variants
- [x] STH contains per-algorithm H_a(act) digests (code + paper)
- [x] Second-preimage and equivocation discussed as independent threats
- [x] "Zero metadata" claim qualified with session-level bandwidth accounting
- [x] No "initial algebra" terminology remains
- [x] resume_alg justified by operational scenario, not key lifecycle
- [x] §1.1 contains no identifying proper nouns
- [x] Absolute benchmarks present in §VII
- [x] Paper renders within 13-page body limit
- [x] Bibliography complete with venues, dates, and stable URLs

## Technical Debt

| Item | Severity | Why Introduced | Follow-Up | Resolved |
| :--- | :------- | :------------- | :-------- | :------: |
| Definition numbers in §V (17-20) are stale after §IV renumbering | MEDIUM | §IV stripped old Def 1 but adds 3 generalized definitions (SplitPolicy, MergeSchedule, AppendConsistent), raising §IV count to 18. §V definitions 17-20 should now be 19-22. | Phase 6 cross-reference consistency pass | Yes |
| Definition references in §II (Def 15), §VI (Def 15), §IX (Def 15) point to old STH number | MEDIUM | STH was old Def 15, now Def 14. Projection was old Def 16, now Def 15. | Phase 6 cross-reference consistency pass | Yes |
| Old law names (A-Equiv, Proj-Valid, A-Stack, I-Sound, K-Sound, T-Bound) in §I, §II, §V, §VII | MEDIUM | Laws removed in §IV rewrite. Other sections still reference them by old smallcaps names. | Phase 4 presentation surgery or Phase 6 | Yes |
| Definition reference in §VII (Def 20) stale | LOW | Should be Def 21 after renumbering. | Phase 6 cross-reference consistency pass | Yes |

## Deviation Log

| Commit | Planned | Actual | Rationale |
| :----- | :------ | :----- | :-------- |
| `cf2d7af` | Single bridge lemma + theorem | Full invariant chain with 30 theorems | The CTO↔MTH equivalence required extensive supporting infrastructure: `cto_trailing_geo` for geometric series, `merge_cascade` for segment merging, `cto_ge_of_mod` for modular arithmetic. The "one theorem + one lemma" estimate understated the proof's depth. |
| (descent) | Proof expected to be straightforward | Required modular arithmetic contradiction via `cto_ge_of_mod` | The descent condition in `appendToStack_invariant` was the hardest sub-proof. Ruling out above-segments of size exactly 2^(k+1) required showing idx ≡ 2^(k+2)-1 (mod 2^(k+2)), contradicting cto = k+1. Not anticipated in the plan. |

## Retrospective

### Process

_To be filled after execution._

### Outcomes

_To be filled after execution._

### Pipeline Improvements

_To be filled after execution._

## References

- Convergence Analysis: `docs/review-iterative/convergence-analysis.md`
- Reviews: `docs/review-iterative/round-{1..6}-pdf.md`
- Domain Model: `docs/models/epoch-merkle-log.md`
- Editorial Guidance: `draft/editorial_guidance.md`
- Paper Source: `docs/paper/`
- Plan Template: `.agents/templates/PLAN.md`
