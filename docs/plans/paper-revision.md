# PLAN: EML Paper Revision — Post-Review Overhaul

## Goal

Address all verified defects and convergent reviewer concerns from
`docs/review-iterative/convergence-analysis.md` to bring the EML paper to
publishable quality for USENIX Security. The revision fixes mathematical
correctness errors, eliminates formalism theatre, tightens security claims,
strips editorial bloat, and adds the empirical baselines reviewers demanded —
while preserving the three contributions that all 6 reviewers praised (temporal
null-padding, deterministic proof elision, evaluation methodology).

## Constraints

- 13-page body (USENIX Security two-column, 10pt)
- The Rust implementation is ground truth — the paper describes what the code does
- Double-blind review
- Page budget is already tight; every addition must be offset by cuts
- Per-algorithm manifest digests (H_a(act)) will be implemented in the crate

## Decisions

| Decision | Choice | Rationale |
| :------- | :----- | :-------- |
| Formal model scope | Radical strip: formalize only novel contributions (~7 definitions + 2 theorems) | The formal model is proof apparatus for Contribution 1, not a standalone contribution. "Initial algebra with 9 equational laws" is the root cause of the "formalism theatre" critique (6/6 reviewers). Standard Merkle tree properties inherited from RFC 9162 do not need restating for a USENIX audience. The domain model in `docs/models/` retains the full specification for implementation. |
| Critical-path deliverable | Lean4 machine-checked proof of Projection Equivalence | 6/6 reviewers flagged the proof as deficient (circularity, missing bridge lemma, base case typo). Machine-checked proof eliminates the entire "eyeball error" category permanently. Every reviewer listed machine-checked proofs as future work — delivering one now is a significant differentiator and moves it from §IX future work to §I contributions. |
| Contribution 2 reframing | "A machine-checked proof (Lean4) reducing multi-algorithm verification to RFC 9162" instead of "an initial algebra over 20 definitions with 9 equational laws" | Specific, mechanically verified claim > volume count. Moves machine-checked proofs from §IX future work to §I contributions. Every reviewer listed this as future work — delivering it now is a differentiator. |
| D-Sep formulation | Computational hardness under ROM | 4/6 flagged Pigeonhole violation. Current statement is mathematically false for unbounded d ∈ Bytes. |
| H(act) weakest-link | Implement per-algorithm H_a(act) manifest digests | 6/6 flagged this. Paper-only acknowledgment is insufficient. Implementation change is small and eliminates the strongest architectural objection. |
| Absolute benchmarks | Implement comparative benchmark (EML vs vanilla RFC 9162) | 5/6 demanded throughput numbers. "We deliberately avoid micro-benchmarks" was identified as evasion. |
| resume_alg | Keep, but reframe justification | The operational scenario (temporary deactivation/reactivation) is legitimate and the implementation supports it. Cutting it from the paper while the code supports it is dishonest. Reframe away from "key lifecycle" (which invites the layer violation critique) toward operational algorithm lifecycle management. |
| §1.1 Case Study | Keep, genericize | The heterogeneous-device scenario is genuinely motivating. Strip "Cyphr" and "Cyphrpunk LLC" proper nouns (double-blind violation). Frame as "long-lived key directories and decentralized identity registries" — the class, not the instance. |
| "Isomorphism" | Rename to "Projection Equivalence" | 3/6 flagged mathematical misuse. π_a is surjective but non-injective; "isomorphism" is wrong. |
| MTH notation | Introduce explicit clarification that Theorem 1's MTH operates on digest sequences | 1/6 flagged as "mathematically false"; verified as false alarm by implementation, but the notation genuinely is ambiguous. Clarify, don't rename. |

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

- ~~Lean4 machine-checked proof of Projection Equivalence and Temporal Binding (`proofs/lean/`)~~ **DONE**
- Radical restructure of `_04-formal-model.qmd`: strip to novel formalisms + Lean4-backed proofs
- ~~Lean proof of Projection Equivalence (standalone document, then integrated)~~ **DONE** — proof covers full chain from CTO primitives through bridge lemma to projection equivalence and temporal binding
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
  - [x] `ctoRoot(projectDigests epochs payloads) = mth(projectDigests epochs payloads)`
  - [x] Follows from bridge lemma applied to the projected leaf sequence
- [x] Prove Temporal Binding (Theorem 2) — `temporal_binding`
  - [x] Reduce to domain separation + Projection Equivalence
  - [x] Inactive positions have null-padded digests; no payload `d` satisfies `leafHash d = nullHash`
- [ ] Definitional correspondence audit: document side-by-side mapping of each Lean definition to its Rust counterpart (`mth`, `cto`, `buildStackAux`, `leafValue`, `project`)
- [ ] Write companion prose document at `docs/proofs/projection-equivalence.md` explaining the proof structure for paper integration

**Proof statistics**: ~1565 lines, 30 theorems, 0 sorry. Build: 3288 jobs, clean.

**Key proof artifacts** (in `proofs/lean/EMLProof/ProjectionEquivalence.lean`):

| Theorem | Line | Statement |
| :------ | :--- | :-------- |
| `bridge_lemma` | 1500 | `ctoRoot leaves = mth leaves` — incremental root = batch root |
| `projection_equivalence` | 1544 | Full EML projection equivalence over epoch/payload sequences |
| `temporal_binding` | 1563 | Inactive positions reject all payloads under domain separation |
| `appendToStack_invariant` | 911 | Core induction: stack invariant preserved on leaf append |
| `merge_cascade` | 865 | Geometric merge run produces MTH over concatenated segments |
| `cto_trailing_geo` | 753 | CTO = k+1 implies trailing k+1 segments are 2⁰..2ᵏ |

---

### Phase 2: Formal Model Restructure — rewrite §IV

- [ ] Strip "initial algebra" and "carrier types" framing
- [ ] Retain only novel definitions:
  - [ ] Null constants (N₀, Nₕ)
  - [ ] Activation map + active predicate + active set
  - [ ] Leaf value function V(a,i)
  - [ ] Projection π_a(S)
  - [ ] Definition of `tree_size(a)` for frozen algorithms
- [ ] Inherited RFC 9162 definitions: brief inline references, not restated as numbered definitions
  - [ ] Hash operations: "We adopt the MTH construction from RFC 9162 (§2.1)" with equation references to §II
  - [ ] Domain separation: stated as a property of the prefix scheme, not an equational law
  - [ ] State tuple, append, root extraction: described informally in §III, referenced from §IV
- [ ] Theorems with proofs:
  - [ ] **Theorem 1** (Projection Equivalence): integrate proof from Phase 1; reference Lean4 mechanization
  - [ ] **Theorem 2** (Temporal Binding): proof sketch reducing to D-Sep + Theorem 1; mechanized in Lean4
  - [ ] Note in §IV that proofs are machine-checked (cite Lean4 artifact)
- [ ] Assumptions (moved to §II Threat Model):
  - [ ] Domain separation as computational hardness under ROM (not absolute quantifier)
  - [ ] Algorithm independence (mutual incompressibility under ROM)
- [ ] Corollaries:
  - [ ] Inclusion/consistency soundness as one-sentence reductions to Theorem 1 + RFC 9162
  - [ ] Projection validity as direct consequence of Theorem 1
  - [ ] Manifest commitment (M-Commit)
- [ ] Clarify MTH notation: explicit note that Theorem 1's MTH operates on pre-hashed digest sequences
- [ ] Rename "Projection Isomorphism" → "Projection Equivalence"
- [ ] Update contribution list in §I: replace "initial algebra, 20 definitions, 9 equational laws" with "formal proof reducing multi-algorithm verification to single-algorithm RFC 9162 verification"

---

### Phase 3: Security & Architecture Fixes — precision in claims

- [ ] Implement per-algorithm H_a(act) manifest digests
  - [ ] Update STH definition (Def 15) to include H_a(act) in per-algorithm tuple
  - [ ] Update M-Commit corollary
  - [ ] Update `docs/models/epoch-merkle-log.md`
  - [ ] Implementation changes in Rust crate
- [ ] Separate second-preimage/equivocation conjunction in §II
  - [ ] Silent payload substitution requires only second-preimage — monitors detect nothing
  - [ ] Equivocation (inconsistent views) is an independent, detectable threat
  - [ ] Remove the "not only... but also" conjunction
- [ ] Fix "zero per-proof metadata" claim in §VI
  - [ ] Acknowledge session-level bandwidth cost: O(|A| · epochs) for act map
  - [ ] Distinguish per-proof wire overhead (eliminated) from session-level state (required)
  - [ ] Update Table 3 with footnote
- [ ] Clarify elision rehydration for non-power-of-two siblings in §VI
  - [ ] Add parenthetical: proof-path siblings cover power-of-two leaf counts
  - [ ] Reference Definition 17 Case 3 for general decomposition
- [ ] Reframe resume_alg justification in §III
  - [ ] Decouple from "key lifecycle" framing
  - [ ] Frame as operational algorithm lifecycle flexibility
  - [ ] Acknowledge complexity cost honestly

---

### Phase 4: Presentation Surgery — reclaim page budget

- [ ] Cut §4.1 Carrier Types entirely (inline ℕ, Bytes, etc. where first used)
- [ ] Cut or radically condense §8.5 Post-Quantum (one sentence in §IX future work)
- [ ] Replace/reduce marketing prose:
  - [ ] "structural crisis" → objective description of operational overhead
  - [ ] "upgrade trilemma" — keep as defined term but reduce repetition frequency
  - [ ] "distributed systems nightmare" → cut
  - [ ] "faithful representation of temporal reality" → cut
- [ ] Fix bibliography:
  - [ ] [1] CARAF: add venue/date
  - [ ] [2] Chopra: add venue/date
  - [ ] [3] Collier: add venue/date or reclassify as technical report
  - [ ] Add missing Bernstein citation for cryptographic agility critique
  - [ ] Fix all grey literature references with stable URLs
- [ ] Genericize §1.1: strip "Cyphr" and "Cyphrpunk LLC"; frame as class of applications
- [ ] Fix Table 2: "amortized O(log K)" → "worst-case O(log K)" for algorithm addition
- [ ] Fix interval notation: Definition 5 open interval → half-open [s_k, e_k) to match Definition 6
- [ ] Trim Ethical Considerations to minimum viable compliance text

---

### Phase 5: Benchmarks — the empirical gap

- [ ] Implement comparative benchmark harness
  - [ ] EML append throughput vs vanilla RFC 9162 (single-algorithm) append throughput
  - [ ] Proof generation latency comparison
  - [ ] Storage amplification measurement (bytes per million entries, by algorithm count)
- [ ] Integrate results into §VII
  - [ ] Replace or supplement complexity regression with absolute numbers
  - [ ] Add benchmark figure(s)
- [ ] Update §7.6 Limitations to remove the "we deliberately avoid micro-benchmarks" evasion

---

### Phase 6: Integration & Verification — final consistency pass

- [ ] Verify contribution list in §I matches actual proven/demonstrated content
  - [ ] Contribution 2 references machine-checked Lean4 proof, not "algebraic model"
- [ ] Verify all definition/theorem numbering is sequential and cross-referenced correctly
- [ ] Cross-check formal model against `docs/models/epoch-merkle-log.md`; update model
- [ ] Update `draft/editorial_guidance.md` to reflect new formal structure
- [ ] Prepare Lean4 artifact for USENIX supplementary material submission
  - [ ] Clean up `proofs/lean/` for external review
  - [ ] Write README with build instructions and theorem inventory
- [ ] Draft Open Science appendix content referencing Lean4 artifact and Rust crate
- [ ] Render PDF and verify body ≤ 13 pages
- [ ] Run quality checkpoints from editorial guidance
- [ ] Full read-through for terminological consistency (terminology lock)

## Verification

- [x] Lean4 proof of Projection Equivalence type-checks successfully
- [x] Lean4 proof of Temporal Binding type-checks successfully
- [ ] Lean4 proof artifact included in supplementary materials
- [ ] No "Law" in §IV — all properties are definitions, assumptions, proved theorems, or corollaries
- [ ] D-Sep stated as computational hardness, not absolute universal quantifier
- [ ] MTH notation unambiguous between raw-payload and digest-domain variants
- [ ] STH contains per-algorithm H_a(act) digests (code + paper)
- [ ] Second-preimage and equivocation discussed as independent threats
- [ ] "Zero metadata" claim qualified with session-level bandwidth accounting
- [ ] No "initial algebra" terminology remains
- [ ] resume_alg justified by operational scenario, not key lifecycle
- [ ] §1.1 contains no identifying proper nouns
- [ ] Absolute benchmarks present in §VII
- [ ] Paper renders within 13-page body limit
- [ ] Bibliography complete with venues, dates, and stable URLs

## Technical Debt

| Item | Severity | Why Introduced | Follow-Up | Resolved |
| :--- | :------- | :------------- | :-------- | :------: |

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
