import EMLProof.Spine
import Mathlib.Data.Nat.Log

/-!
# K-ary log-spine topology and verifier soundness (V9)

This module closes the V9 gap: the k-ary construction, the base-k carry
schedule, and the inclusion verifier were previously unmodeled — "formally
proven" covered only the honest binary construction, not the adversarial
input path.

Three layers, mirroring the shipped Rust:

1. **Topology** (`frontierForSizeT`, `reductionCount`, `inclusionSkeleton`):
   total transcriptions of `spine/src/topology.rs`. The legacy `partial def`
   models earlier in the corpus (`frontierForSize`, `buildTree`,
   `reconstructIndexFromPath` in `Spine.lean`) are opaque to the kernel and
   admit no theorems; these replace them as proof subjects. Deviation from
   Rust: the `k ≤ 256`, `path.len() ≤ 256` and digest-length DoS bounds are
   dropped — they bound resource use, not the security argument.

2. **Construction** (`buildStackCells`, `perfectRoot`, `karyRoot`): the
   frontier stack machine of `append_leaf`/`append_subtree` (push, then
   `reduction_count` merges of the top `k` via null-promoting `nary_mr`) and
   the canonical perfect-subtree decomposition it must agree with. The
   k-ary bridge lemma (`kary_bridge`) is the k-ary `AppendConsistent`
   analog: the shipped `frontier_for_size` + `reduction_count` schedule is
   consistent — previously proven for no real policy (only the degenerate
   `linear_split_policy` in `General/Instantiation.lean`, and only for
   binary nodes).

3. **Verifier** (`AcceptsKary`, `kary_inclusion_soundness`,
   `kary_completeness`): a faithful model of
   `reconstruct_inclusion_root`/`verify_inclusion_path_structure`
   (`spine/src/proof.rs`): the trailing steps are pinned field-by-field
   against `inclusionSkeleton`; zero-sibling (promoted) steps are rejected;
   the fold is the null-promoting `naryMr`, NOT plain `nodeHash` — the
   existing `foldCanonical` model elides null promotion, which is exactly
   where a sloppy statement would go vacuous or false.

Soundness is **existential in depth**: an accepting proof binds the leaf to
the level-0 cell at log position `index` through *some* number `d` of
within-subtree prefix steps; depth inside the subtree is never bound
(Cyphr SPEC §2.2.12). Soundness is derived as completeness + uniqueness:
the honest path for `index` accepts (`kary_completeness` — also the
non-vacuity witness for `AcceptsKary`), and two accepting paths of equal
shape folding to the same root coincide step-by-step unless a hash
assumption breaks (`foldNary_unique_of_shape`).

## Hash assumptions

Collision-style escape hatches, matching the corpus convention
(`HashCollision`, `NodeHashCollision`):

* `NodeHashCollision` — distinct child lists, equal `nodeHash`.
* `CollapseAmbiguity` — some node of ≥ 2 *not-all-equal* children hashes to
  a value `v` that an all-equal-to-`v` run collapses to. With untagged
  `nodeHash = H(concat)` this is `H(child bytes) = v`, i.e. an `H` collision
  unless the child bytes literally concatenate to the `v`-run preimage
  (impossible for real digest widths, but `digestToBytes` is an axiom with no
  length constraint, so it is surfaced honestly as its own assumption). The
  all-null instance (`v = nullDigest`) is the dominant case in a sparse log.

## Status

All theorems in this module are proven `sorry`-free: the topology
(`frontier_tiles`, `skeleton_no_promoted`), the carry schedule
(`frontier_append_consistent`), the construction (`kary_bridge`), and the
verifier (`kary_completeness`, `kary_inclusion_soundness`). The two hash
assumptions appear only as explicit hypotheses (`¬NodeHashCollision`,
`¬CollapseAmbiguity`), never as axioms.
-/

set_option linter.style.emptyLine false
set_option linter.unusedVariables false

namespace NEML

/-!
## Rust correspondence

This module is a hand transcription of the shipped Rust, so its soundness for
the *real* system rests on the Lean definitions faithfully mirroring it. This
section makes that mapping auditable: every Lean symbol below names the Rust
it models with a `file:line` anchor, and each row states **how** the
correspondence is checked — `#guard`-pinned (mechanically, via a `#guard` here
with a value-for-value twin in `topology.rs::tests::lean_guard_parity`) or
**inspection-only** (a structural reading a human must perform). Line numbers
are anchors, not guarantees; re-locate by symbol name if they drift.

### Layer 1 — computable topology (`#guard`-pinned)

Pure `Nat`/`List` arithmetic, so it can be and is pinned by evaluation. The
guard set exercises all of these — `inclusionSkeleton` guards drive
`findFrontier`, `digitSteps`, and `groupingSteps` end-to-end — so a value
disagreement on any of them fails a build on both sides.

| Lean | Rust | Pinning |
| --- | --- | --- |
| `frontierForSizeT` / `frontierGo` | `frontier_for_size` (`spine/src/topology.rs:20`) | pinned — 3 guard vectors |
| `reductionCount` / `reductionCountGo` | `reduction_count` (`cml/src/schedule.rs:11`) | pinned — 2 guard vectors |
| `inclusionSkeleton` | `inclusion_skeleton` (`spine/src/topology.rs:66`) | pinned — 6 guard vectors |
| `findFrontier` | subtree-locate loop in `inclusion_skeleton` (`spine/src/topology.rs:77`) | pinned transitively |
| `digitSteps` | base-k offset-digit loop in `inclusion_skeleton` (`spine/src/topology.rs:92`) | pinned transitively |
| `groupingSteps` | `grouping_steps` (`spine/src/topology.rs:118`) | pinned transitively |
| `stepShape` | `SkeletonStep {position, sibling_count}` (`spine/src/topology.rs:46`); compared in `verify_inclusion_path_structure` (`spine/src/proof.rs:507`) | pinned — guard pairs *are* `(position, siblingCount)` |

### Layers 2–3 — noncomputable fold / accept (inspection-only)

Built on the `H : List UInt8 → Digest` axiom, so they cannot be
`#guard`-evaluated — that is a category limit, not an omission. Each row is a
structural reading of the Rust that a reviewer must confirm; the `#guard`s do
**not** reach here.

| Lean | Rust | Notes (inspection-only) |
| --- | --- | --- |
| `naryMr` | `nary_mr` (`spine/src/mr.rs:11`) | empty→`empty()`, singleton→child unchanged, all children equal→that value (general collapse; all-null→`null()` the dominant instance), else `node(children)` |
| `mergeTopD` / `mergeTopDN` / `appendCell` / `buildStackGo` / `buildStackCells` | push-then-merge loop in `append_leaf` / `append_subtree` (`cmt/src/tree.rs:925`, merge via `nary_mr` at `:949`) | push the cell, run `reduction_count` merges of the top `k` |
| `perfectRoot` | the canonical perfect-subtree fold that same loop realizes (no standalone Rust fn) | `kary_bridge` proves the stack machine equals this decomposition |
| `foldFrontierRoot` / `karyRoot` | `compute_root_from_state` (`cmt/src/tree.rs:315`) | merge rightmost `k` while `> k` remain, then one final `nary_mr` |
| `StructureOK` | `verify_inclusion_path_structure` (`spine/src/proof.rs:489`) | skeleton exists, `path.len ≥ skel.len`, trailing `skel.len` steps match shape (the skeleton it pins against is itself guard-pinned; this relation is not) |
| `WellFormedSteps` | per-step guards in `reconstruct_inclusion_root` (`spine/src/proof.rs:561` zero-sibling reject, `:569` position bound) | canonical encoding |
| `applyStepN` / `foldNary` | reconstruction fold in `reconstruct_inclusion_root` (`spine/src/proof.rs:550`; child-list build `:574`, `nary_mr` at `:585`) | `insertAt` ⟷ inserting `current` at `position` among siblings |
| `AcceptsKary` | `verify_inclusion` (`spine/src/proof.rs:77`) → `reconstruct_inclusion_root` | the model drops only the DoS bounds (digest length, `path.len ≤ 256`, `siblings.len ≤ 256`), which bound resource use, not soundness |

**Residual risk this note does not close.** The Layer 2–3 rows above are
verified by human reading alone. Nothing mechanical forces `naryMr`,
`foldNary`, the builder loop, or `AcceptsKary` to keep matching their Rust
counterparts: an edit to `nary_mr`, `reconstruct_inclusion_root`, or the
`append_*` merge loop that diverges from these definitions would leave every
theorem in this file true *of the Lean model* while silently false *of the
shipped Rust*, and no build — Lean or Rust — would fail. The `H`-axiom backing
makes this irreducible here; only a computable hash instantiation plus
differential execution against the Rust could pin it. Treat these rows as a
documented, standing assumption, not a discharged one.

## Layer 1 — topology (total transcription of `spine/src/topology.rs`) -/

/-- Greedy frontier decomposition from `left` over `n` remaining leaves:
    repeatedly strip the largest perfect k-ary subtree (`cap = k ^ log_k n`).
    Mirrors the inner loop of `frontier_for_size`. -/
def frontierGo (k left n : Nat) : List (Nat × Nat) :=
  if h : n = 0 ∨ k < 2 then []
  else
    (left, Nat.log k n) ::
      frontierGo k (left + k ^ Nat.log k n) (n - k ^ Nat.log k n)
termination_by n
decreasing_by
  push_neg at h
  have hcap : 0 < k ^ Nat.log k n := pow_pos (by omega) _
  omega

/-- Frontier of a log of `n` leaves at arity `k`: `(left, height)` per perfect
    k-ary subtree, left to right. Total counterpart of the legacy
    `partial def frontierForSize`; mirrors `topology.rs::frontier_for_size`. -/
def frontierForSizeT (k n : Nat) : List (Nat × Nat) := frontierGo k 0 n

/-- Carry count of the append at 0-based index `n`: the multiplicity of `k`
    in `n + 1`. Mirrors `reduction_count` (`cml/src/schedule.rs`):
    after pushing leaf `n`, the builder merges the top `k` stack entries
    this many times. -/
def reductionCountGo (k m : Nat) : Nat :=
  if h : 2 ≤ k ∧ 0 < m ∧ m % k = 0 then 1 + reductionCountGo k (m / k) else 0
termination_by m
decreasing_by
  exact Nat.div_lt_self h.2.1 (by omega)

/-- `reductionCount k n` = number of top-k merges after appending index `n`. -/
def reductionCount (k n : Nat) : Nat := reductionCountGo k (n + 1)

/-- One coordinate-level merge: replace the last `k` frontier coordinates by
    their parent `(left of the k-th-from-last, height + 1)`. No-op below `k`
    entries (the schedule consistency theorem shows that case never fires
    under `reductionCount`). The merged entries having equal heights is a
    *theorem* (`frontier_append_consistent`), not baked into the def. -/
def mergeTopCoords (k : Nat) (coords : List (Nat × Nat)) : List (Nat × Nat) :=
  if coords.length < k then coords
  else
    match (coords.drop (coords.length - k)).head? with
    | none => coords
    | some (l, h) => coords.take (coords.length - k) ++ [(l, h + 1)]

/-- Iterated coordinate merge. -/
def mergeTopCoordsN (k : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, cs => cs
  | c + 1, cs => mergeTopCoordsN k c (mergeTopCoords k cs)

/-- `Tiles k start coords stop`: the coordinates tile `[start, stop)` with
    consecutive spans `[left, left + k^height)`. The frontier's defining
    structural property; consumed by skeleton location and the bridge. -/
def Tiles (k : Nat) : Nat → List (Nat × Nat) → Nat → Prop
  | start, [], stop => start = stop
  | start, (l, h) :: rest, stop => l = start ∧ Tiles k (start + k ^ h) rest stop

/-- Generalized coverage: the greedy decomposition from `left` over `n`
    remaining leaves tiles `[left, left + n)`. -/
private theorem frontierGo_tiles (k : Nat) (hk : 2 ≤ k) :
    ∀ n left, Tiles k left (frontierGo k left n) (left + n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro left
    rw [frontierGo]
    split
    · next h =>
        have hn : n = 0 := by omega
        subst hn
        simp [Tiles]
    · next h =>
        push_neg at h
        obtain ⟨hn0, _⟩ := h
        have hcap : k ^ Nat.log k n ≤ n := Nat.pow_log_le_self k hn0
        have hcappos : 0 < k ^ Nat.log k n := pow_pos (by omega) _
        refine ⟨rfl, ?_⟩
        have hrec := ih (n - k ^ Nat.log k n) (by omega) (left + k ^ Nat.log k n)
        have harith : (left + k ^ Nat.log k n) + (n - k ^ Nat.log k n) = left + n := by omega
        rw [harith] at hrec
        exact hrec

/-- **Frontier coverage.** The frontier tiles `[0, n)`. -/
theorem frontier_tiles (k n : Nat) (hk : 2 ≤ k) :
    Tiles k 0 (frontierForSizeT k n) n := by
  have := frontierGo_tiles k hk n 0
  simpa [frontierForSizeT] using this

/-! Helper arithmetic for the carry schedule: the frontier is governed by the
    base-`k` digit expansion, so appends factor through division by `k`
    (`frontierGo_scale`), single pushes (`frontierGo_push`), and the digit
    decomposition (`frontier_divstep`). -/

/-- Every left coordinate in `frontierGo k off n` is at least `off`. -/
private theorem frontierGo_left_ge (k : Nat) (hk : 2 ≤ k) :
    ∀ (n off : Nat), ∀ lh ∈ frontierGo k off n, off ≤ lh.1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro off lh hmem
    rw [frontierGo] at hmem
    split at hmem
    · simp only [List.not_mem_nil] at hmem
    · next h =>
        push_neg at h
        obtain ⟨hn0, _⟩ := h
        rw [List.mem_cons] at hmem
        have hcappos : 0 < k ^ Nat.log k n := pow_pos (by omega) _
        rcases hmem with rfl | hmem'
        · exact le_refl _
        · have := ih (n - k ^ Nat.log k n) (by
            have : k ^ Nat.log k n ≤ n := Nat.pow_log_le_self k hn0; omega)
            (off + k ^ Nat.log k n) lh hmem'
          omega

/-- Multiplying the leaf count by `k` raises every frontier subtree one level
    and scales its span by `k`. General over both offsets so the induction
    closes. -/
private theorem frontierGo_scale (k : Nat) (hk : 2 ≤ k) :
    ∀ (j left off : Nat),
      frontierGo k left (j * k) =
        (frontierGo k off j).map (fun lh => (left + (lh.1 - off) * k, lh.2 + 1)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro left off
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; simp [frontierGo]
    · have hjk : j * k ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
      have hcapj : k ^ Nat.log k j ≤ j := Nat.pow_log_le_self k (by omega)
      have hcapjpos : 0 < k ^ Nat.log k j := pow_pos (by omega) _
      have hlog : Nat.log k (j * k) = Nat.log k j + 1 := Nat.log_mul_base (by omega) (by omega)
      have hunfoldL : frontierGo k left (j * k) =
          (left, Nat.log k j + 1) ::
            frontierGo k (left + k ^ Nat.log k j * k) ((j - k ^ Nat.log k j) * k) := by
        conv_lhs => rw [frontierGo]
        rw [dif_neg (by omega), hlog, pow_succ, ← Nat.sub_mul]
      have hunfoldR : frontierGo k off j =
          (off, Nat.log k j) :: frontierGo k (off + k ^ Nat.log k j) (j - k ^ Nat.log k j) := by
        conv_lhs => rw [frontierGo]
        rw [dif_neg (by omega)]
      rw [hunfoldL, hunfoldR, List.map_cons]
      refine List.cons_eq_cons.mpr ⟨by simp, ?_⟩
      rw [ih (j - k ^ Nat.log k j) (by omega) (left + k ^ Nat.log k j * k)
        (off + k ^ Nat.log k j)]
      apply List.map_congr_left
      intro lh hlh
      have hge : off + k ^ Nat.log k j ≤ lh.1 :=
        frontierGo_left_ge k hk (j - k ^ Nat.log k j) (off + k ^ Nat.log k j) lh hlh
      rw [Prod.mk.injEq]
      refine ⟨?_, rfl⟩
      have hrw : (lh.1 - off) * k =
          (lh.1 - (off + k ^ Nat.log k j)) * k + k ^ Nat.log k j * k := by
        rw [← Nat.add_mul]; congr 1; omega
      rw [hrw]; omega

/-- Scale at the canonical origin: `frontierForSizeT k (a*k)` is the frontier of
    `a` with every span scaled and every height bumped. -/
private theorem frontierForSizeT_scale (k : Nat) (hk : 2 ≤ k) (a : Nat) :
    frontierForSizeT k (a * k) =
      (frontierForSizeT k a).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) := by
  rw [frontierForSizeT, frontierForSizeT, frontierGo_scale k hk a 0 0]
  apply List.map_congr_left
  intro lh _
  simp

/-- A push that does not complete a `k`-group just appends a height-0 leaf. -/
private theorem frontierGo_push (k : Nat) (hk : 2 ≤ k) :
    ∀ (n left : Nat), (n + 1) % k ≠ 0 →
      frontierGo k left (n + 1) = frontierGo k left n ++ [(left + n, 0)] := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro left hmod
    have hmono : Nat.log k n ≤ Nat.log k (n + 1) := Nat.log_mono_right (by omega)
    have hlogeq : Nat.log k (n + 1) = Nat.log k n := by
      rcases Nat.lt_or_ge (Nat.log k n) (Nat.log k (n + 1)) with hlt | hge
      · exfalso
        have hle : k ^ (Nat.log k n + 1) ≤ n + 1 :=
          le_trans (Nat.pow_le_pow_right (by omega) hlt) (Nat.pow_log_le_self k (by omega))
        have hgt : n < k ^ (Nat.log k n + 1) := Nat.lt_pow_succ_log_self (by omega) n
        have heq1 : n + 1 = k ^ (Nat.log k n + 1) := by omega
        apply hmod
        rw [heq1, pow_succ, Nat.mul_comm]
        exact Nat.mul_mod_right k _
      · omega
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hlog1 : Nat.log k 1 = 0 := by rw [Nat.log_eq_zero_iff]; omega
      rw [frontierGo, dif_neg (by omega), hlog1, pow_zero]
      simp [frontierGo]
    · have hcap : k ^ Nat.log k n ≤ n := Nat.pow_log_le_self k (by omega)
      have hcappos : 0 < k ^ Nat.log k n := pow_pos (by omega) _
      have hsubmod : (n - k ^ Nat.log k n + 1) % k ≠ 0 := by
        rcases Nat.eq_zero_or_pos (Nat.log k n) with hl0 | hlpos
        · rw [hl0, pow_zero]
          have hnlt : n < k := by
            have h := Nat.lt_pow_succ_log_self (show 1 < k by omega) n
            rw [hl0] at h; simpa using h
          rw [show n - 1 + 1 = n by omega, Nat.mod_eq_of_lt hnlt]; omega
        · obtain ⟨c, hc⟩ : k ∣ k ^ Nat.log k n := dvd_pow_self k (by omega)
          have hkey : n + 1 = (n - k ^ Nat.log k n + 1) + k * c := by rw [← hc]; omega
          rw [hkey, Nat.add_mul_mod_self_left] at hmod
          exact hmod
      have hunfold1 : frontierGo k left (n + 1) =
          (left, Nat.log k n) ::
            frontierGo k (left + k ^ Nat.log k n) (n + 1 - k ^ Nat.log k n) := by
        conv_lhs => rw [frontierGo]
        rw [dif_neg (by omega), hlogeq]
      have hunfold2 : frontierGo k left n =
          (left, Nat.log k n) :: frontierGo k (left + k ^ Nat.log k n) (n - k ^ Nat.log k n) := by
        conv_lhs => rw [frontierGo]
        rw [dif_neg (by omega)]
      rw [hunfold1, hunfold2, List.cons_append]
      refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
      rw [show n + 1 - k ^ Nat.log k n = (n - k ^ Nat.log k n) + 1 by omega,
        ih (n - k ^ Nat.log k n) (by omega) (left + k ^ Nat.log k n) hsubmod,
        show left + k ^ Nat.log k n + (n - k ^ Nat.log k n) = left + n by omega]

/-- Canonical-origin push corollary. -/
private theorem frontierForSizeT_push (k : Nat) (hk : 2 ≤ k) (m : Nat)
    (hmod : (m + 1) % k ≠ 0) :
    frontierForSizeT k (m + 1) = frontierForSizeT k m ++ [(m, 0)] := by
  have := frontierGo_push k hk m 0 hmod
  simpa [frontierForSizeT] using this

/-- **Digit decomposition (one base-`k` division step).** For `b < k`, the
    frontier of `a*k + b` is the scaled frontier of `a` followed by `b`
    height-0 leaves. `b = 0` is the scale lemma; the step is a push. -/
private theorem frontier_divstep (k : Nat) (hk : 2 ≤ k) (a : Nat) :
    ∀ b, b < k → frontierForSizeT k (a * k + b) =
      (frontierForSizeT k a).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) ++
      (List.range b).map (fun i => (a * k + i, 0)) := by
  intro b
  induction b with
  | zero =>
    intro _
    simp only [Nat.add_zero, List.range_zero, List.map_nil, List.append_nil]
    exact frontierForSizeT_scale k hk a
  | succ b ih =>
    intro hb
    have hb' : b < k := by omega
    have hmod : (a * k + b + 1) % k ≠ 0 := by
      have heqmod : (a * k + b + 1) % k = (b + 1) % k := by
        rw [show a * k + b + 1 = (b + 1) + a * k by ring, Nat.add_mul_mod_self_right]
      rw [heqmod, Nat.mod_eq_of_lt hb]; omega
    rw [show a * k + (b + 1) = (a * k + b) + 1 by ring,
      frontierForSizeT_push k hk (a * k + b) hmod, ih hb', List.append_assoc]
    congr 1
    rw [List.range_succ, List.map_append]
    simp

/-- **Carry-schedule consistency — the k-ary `AppendConsistent`.** Appending
    index `n` (push `(n, 0)`, then `reductionCount k n` top-k merges)
    transforms the frontier of size `n` into the frontier of size `n + 1`.
    This is the property `General/Instantiation.lean` proves for no real
    policy; here it is stated for the *shipped* schedule.

    *Strategy:* both sides are determined by the base-k digit expansion of
    `n` and `n + 1`: the frontier lists height `h` exactly `digit_h(n)`
    times (descending heights), and `reductionCount k n` is the number of
    trailing `k-1` digits of `n` (the carry run of the increment). Prove a
    digit characterization of `frontierGo` first, then the merge recursion
    consumes one trailing-digit run. Pure arithmetic; no hashing. -/
private theorem mergeTopCoords_scale (k : Nat) (cs : List (Nat × Nat)) :
    mergeTopCoords k (cs.map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1))) =
      (mergeTopCoords k cs).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) := by
  unfold mergeTopCoords
  by_cases hlen : cs.length < k
  · simp [List.length_map, hlen]
  · rw [List.length_map, if_neg hlen, if_neg hlen, ← List.map_drop]
    cases hdrop : cs.drop (cs.length - k) with
    | nil => simp
    | cons x rest =>
      obtain ⟨l, h⟩ := x
      simp [List.map_take]

private theorem mergeTopCoordsN_scale (k : Nat) :
    ∀ (c : Nat) (cs : List (Nat × Nat)),
      mergeTopCoordsN k c (cs.map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1))) =
        (mergeTopCoordsN k c cs).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) := by
  intro c
  induction c with
  | zero => intro cs; rfl
  | succ c ih =>
    intro cs
    show mergeTopCoordsN k c (mergeTopCoords k (cs.map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)))) =
         (mergeTopCoordsN k c (mergeTopCoords k cs)).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1))
    rw [mergeTopCoords_scale]
    exact ih (mergeTopCoords k cs)

/-- A single merge of a trailing run of exactly `k` height-0 leaves at
    consecutive positions `b, b+1, …, b+k-1` produces one height-1 node at
    `b`, leaving the prefix untouched. -/
private theorem mergeTopCoords_group (k : Nat) (hk : 1 ≤ k) (P : List (Nat × Nat)) (b : Nat) :
    mergeTopCoords k (P ++ (List.range k).map (fun i => (b + i, 0))) = P ++ [(b, 1)] := by
  have hglen : ((List.range k).map (fun i => (b + i, 0))).length = k := by
    rw [List.length_map, List.length_range]
  have hsub : (P ++ (List.range k).map (fun i => (b + i, 0))).length - k = P.length := by
    rw [List.length_append, hglen]; omega
  unfold mergeTopCoords
  rw [if_neg (by rw [List.length_append, hglen]; omega), hsub, List.drop_left]
  rw [show k = (k - 1) + 1 by omega, List.range_succ_eq_map, List.map_cons, List.head?_cons]
  simp [hsub, List.take_left]

theorem frontier_append_consistent (k n : Nat) (hk : 2 ≤ k) :
    frontierForSizeT k (n + 1) =
      mergeTopCoordsN k (reductionCount k n) (frontierForSizeT k n ++ [(n, 0)]) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hmod0 : (n + 1) % k = 0
    · -- Carry case: `n + 1 = m * k`, one group merge then the carries of `m - 1`.
      have hdvd : k ∣ (n + 1) := Nat.dvd_of_mod_eq_zero hmod0
      have hkle : k ≤ n + 1 := Nat.le_of_dvd (by omega) hdvd
      have hn1 : 1 ≤ n := by omega
      set m := (n + 1) / k with hm
      have hmk : m * k = n + 1 := by rw [hm]; exact Nat.div_mul_cancel hdvd
      have hmpos : 0 < m := by rw [hm]; exact Nat.div_pos hkle (by omega)
      have hmlt : m < n + 1 := by rw [hm]; exact Nat.div_lt_self (by omega) (by omega)
      have hmlt' : m - 1 < n := by omega
      have hrceq : reductionCount k n = 1 + reductionCount k (m - 1) := by
        unfold reductionCount
        conv_lhs => rw [reductionCountGo]
        rw [dif_pos ⟨by omega, by omega, hmod0⟩]
        congr 1
        rw [← hm]
        congr 1
        omega
      have hLHS : frontierForSizeT k (n + 1) =
          (frontierForSizeT k m).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) := by
        rw [← hmk, frontierForSizeT_scale k hk m]
      have hn_eq : n = (m - 1) * k + (k - 1) := by rw [Nat.sub_one_mul]; omega
      have hfn : frontierForSizeT k n =
          (frontierForSizeT k (m - 1)).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) ++
          (List.range (k - 1)).map (fun i => ((m - 1) * k + i, 0)) := by
        rw [hn_eq]; exact frontier_divstep k hk (m - 1) (k - 1) (by omega)
      have hrange : List.range k = List.range (k - 1) ++ [k - 1] := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega]
        rw [List.range_succ]
      have hYeq : frontierForSizeT k n ++ [(n, 0)] =
          (frontierForSizeT k (m - 1)).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) ++
          (List.range k).map (fun i => ((m - 1) * k + i, 0)) := by
        rw [hfn, List.append_assoc]
        congr 1
        rw [hrange, List.map_append]
        congr 1
        simp [hn_eq]
      have hgroup := mergeTopCoords_group k (by omega)
        ((frontierForSizeT k (m - 1)).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1))) ((m - 1) * k)
      have hgroup2 :
          (frontierForSizeT k (m - 1)).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) ++ [((m - 1) * k, 1)] =
            (frontierForSizeT k (m - 1) ++ [(m - 1, 0)]).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) := by
        rw [List.map_append, List.map_cons, List.map_nil]
      rw [hrceq, hLHS, hYeq,
        show (1 : Nat) + reductionCount k (m - 1) = reductionCount k (m - 1) + 1 from by omega]
      conv_rhs => rw [mergeTopCoordsN]
      rw [hgroup, hgroup2, mergeTopCoordsN_scale, ← ih (m - 1) hmlt',
        show m - 1 + 1 = m from by omega]
    · -- No-carry case: a plain push, zero merges.
      have hrc0 : reductionCount k n = 0 := by
        unfold reductionCount
        rw [reductionCountGo, dif_neg (by rintro ⟨_, _, h⟩; exact hmod0 h)]
      rw [hrc0]
      show frontierForSizeT k (n + 1) = frontierForSizeT k n ++ [(n, 0)]
      exact frontierForSizeT_push k hk n hmod0

/-- Grouping steps from frontier slot `fIdx` to the spine root: fold the
    frontier by repeatedly merging the rightmost `k` slots; a final group of
    `2..k` merges into the root. Each `(position, childCount)` is one merge
    the target participates in, leaf → root. Mirrors
    `topology.rs::grouping_steps`. -/
def groupingSteps (k len fIdx : Nat) : List (Nat × Nat) :=
  if h : k < 2 ∨ len ≤ k then
    if 1 < len then [(fIdx, len)] else []
  else
    if fIdx ≥ len - k then
      (fIdx - (len - k), k) :: groupingSteps k (len - k + 1) (len - k)
    else
      groupingSteps k (len - k + 1) fIdx
termination_by len
decreasing_by
  all_goals (push_neg at h; omega)

/-- Base-k digit steps inside a perfect subtree of height `h`, low digit
    first (leaf → frontier-node root): `(offset mod k, k - 1)` per level. -/
def digitSteps (k offset : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | h + 1 => (offset % k, k - 1) :: digitSteps k (offset / k) h

/-- Locate the frontier subtree containing `index`:
    returns `(slot, left, height)`. -/
def findFrontier (k index : Nat) : List (Nat × Nat) → Nat → Option (Nat × Nat × Nat)
  | [], _ => none
  | (l, h) :: rest, fIdx =>
    if l ≤ index ∧ index < l + k ^ h then some (fIdx, l, h)
    else findFrontier k index rest (fIdx + 1)

/-- The log-spine inclusion skeleton for `(k, treeSize, index)`: per-step
    `(position, siblingCount)`, leaf → root. The single topology authority,
    shared by generator and verifier. Mirrors
    `topology.rs::inclusion_skeleton`. -/
def inclusionSkeleton (k treeSize index : Nat) : Option (List (Nat × Nat)) :=
  if k < 2 then none
  else
    match findFrontier k index (frontierForSizeT k treeSize) 0 with
    | none => none
    | some (fIdx, l, h) =>
      some (digitSteps k (index - l) h ++
        (groupingSteps k (frontierForSizeT k treeSize).length fIdx).map
          (fun pc => (pc.1, pc.2 - 1)))

/-- Every digit step carries position `< k` and exactly `k - 1` siblings. -/
private theorem digitSteps_spec (k : Nat) (hk : 2 ≤ k) :
    ∀ (h offset : Nat), ∀ pc ∈ digitSteps k offset h, pc.1 < k ∧ pc.2 = k - 1 := by
  intro h
  induction h with
  | zero => intro offset pc hmem; simp only [digitSteps, List.not_mem_nil] at hmem
  | succ n ih =>
    intro offset pc hmem
    simp only [digitSteps, List.mem_cons] at hmem
    rcases hmem with rfl | hmem'
    · exact ⟨Nat.mod_lt offset (by omega), rfl⟩
    · exact ih (offset / k) pc hmem'

/-- Every grouping step has `childCount ∈ [2, k]` and position `< childCount`,
    provided the tracked slot is in range. The slot-in-range invariant is
    preserved by both recursive branches. -/
private theorem groupingSteps_spec (k : Nat) (hk : 2 ≤ k) :
    ∀ (len fIdx : Nat), fIdx < len → ∀ pc ∈ groupingSteps k len fIdx,
      2 ≤ pc.2 ∧ pc.1 < pc.2 := by
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intro fIdx hlt pc hmem
    rw [groupingSteps] at hmem
    split at hmem
    · next hbase =>
        split at hmem
        · next hlen1 =>
            simp only [List.mem_singleton] at hmem
            subst hmem
            exact ⟨by omega, hlt⟩
        · next hlen1 => simp only [List.not_mem_nil] at hmem
    · next hrec =>
        push_neg at hrec
        obtain ⟨_, hlenk⟩ := hrec
        split at hmem
        · next hge =>
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem'
            · exact ⟨by omega, by show fIdx - (len - k) < k; omega⟩
            · exact ih (len - k + 1) (by omega) (len - k) (by omega) pc hmem'
        · next hlt2 => exact ih (len - k + 1) (by omega) fIdx (by omega) pc hmem

/-- `findFrontier` returns a slot strictly within the list (counting from the
    starting counter). -/
theorem findFrontier_slot_lt (k index : Nat) :
    ∀ (l : List (Nat × Nat)) (c fIdx lv h : Nat),
      findFrontier k index l c = some (fIdx, lv, h) → fIdx < c + l.length := by
  intro l
  induction l with
  | nil => intro c fIdx lv h hf; simp only [findFrontier, reduceCtorEq] at hf
  | cons p rest ih =>
    intro c fIdx lv h hf
    obtain ⟨pl, ph⟩ := p
    rw [findFrontier] at hf
    split at hf
    · next hcond =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨hfi, _, _⟩ := hf
        subst hfi
        simp only [List.length_cons]; omega
    · next hcond =>
        have := ih (c + 1) fIdx lv h hf
        simp only [List.length_cons]; omega

/-- **The skeleton never contains a promoted step.** Every step carries at
    least one sibling, and the path-node position is within the arity. This
    is what entitles the verifier to reject zero-sibling steps outright
    (canonical encoding) with no completeness loss.
    *Strategy:* digit steps carry `k - 1 ≥ 1` siblings and position
    `offset % k ≤ k - 1`; grouping steps have `childCount ∈ [2, k]` and
    position `< childCount` by induction on `groupingSteps` (needs
    `fIdx < len`, available from `findFrontier` membership). -/
theorem skeleton_no_promoted (k treeSize index : Nat) (skel : List (Nat × Nat))
    (hskel : inclusionSkeleton k treeSize index = some skel) :
    ∀ pc ∈ skel, 1 ≤ pc.2 ∧ pc.1 ≤ pc.2 := by
  rw [inclusionSkeleton] at hskel
  split at hskel
  · next hk2 => simp only [reduceCtorEq] at hskel
  · next hk2 =>
    have hk : 2 ≤ k := by omega
    cases hff : findFrontier k index (frontierForSizeT k treeSize) 0 with
    | none => rw [hff] at hskel; simp only [reduceCtorEq] at hskel
    | some res =>
      obtain ⟨fIdx, lv, h⟩ := res
      rw [hff] at hskel
      simp only [Option.some.injEq] at hskel
      subst hskel
      intro pc hmem
      rw [List.mem_append] at hmem
      rcases hmem with hd | hg
      · obtain ⟨hpos, hsib⟩ := digitSteps_spec k hk h (index - lv) pc hd
        exact ⟨by rw [hsib]; omega, by rw [hsib]; omega⟩
      · rw [List.mem_map] at hg
        obtain ⟨g, hgmem, hgeq⟩ := hg
        have hfidxlt : fIdx < (frontierForSizeT k treeSize).length := by
          have := findFrontier_slot_lt k index (frontierForSizeT k treeSize) 0 fIdx lv h hff
          simpa using this
        obtain ⟨hg2, hg1⟩ := groupingSteps_spec k hk _ fIdx hfidxlt g hgmem
        rw [← hgeq]
        exact ⟨by show 1 ≤ g.2 - 1; omega, by show g.1 ≤ g.2 - 1; omega⟩

/-! Executable sanity pins against `topology.rs` test vectors: definitional
    drift between this model and the Rust source breaks the build here, not
    silently in a proof. Each `#guard` below has a value-for-value twin in
    `spine/src/topology.rs::tests::lean_guard_parity`, so drift on *either* side
    fails a build. Adding a `#guard` here obliges adding its Rust twin there. -/
section SanityChecks
set_option linter.hashCommand false
#guard frontierForSizeT 2 5 = [(0, 2), (4, 0)]
#guard frontierForSizeT 3 5 = [(0, 1), (3, 0), (4, 0)]
#guard frontierForSizeT 2 0 = []
#guard (List.range 8).map (reductionCount 2) = [0, 1, 0, 2, 0, 1, 0, 3]
#guard (List.range 9).map (reductionCount 3) = [0, 0, 1, 0, 0, 1, 0, 0, 2]
#guard inclusionSkeleton 2 1 0 = some []          -- singleton: empty path
#guard inclusionSkeleton 2 5 4 = some [(1, 1)]    -- lone height-0 node, one grouping step
#guard inclusionSkeleton 2 4 1 = some [(1, 1), (0, 1)]  -- two digit steps, no grouping
#guard inclusionSkeleton 3 4 3 = some [(1, 1)]
#guard inclusionSkeleton 2 4 4 = none             -- index out of range
#guard inclusionSkeleton 1 4 0 = none             -- arity out of range
end SanityChecks

/-! ## Layer 2 — construction: stack machine and canonical decomposition -/

open Classical in
/-- Same-value-collapsing n-ary Merkle root, faithful to `mr.rs::nary_mr`:
    empty → `emptyHash`; singleton → promoted unchanged; otherwise the shared
    value if *all* children are equal (general collapse — the all-null run is its
    dominant instance), else `nodeHash`. The verifier's fold and the builder's
    merge both use this — never plain `nodeHash`. -/
noncomputable def naryMr (children : List Digest) : Digest :=
  match children with
  | [] => emptyHash
  | [c] => c
  | a :: b :: zs => if ∀ c ∈ (a :: b :: zs), c = a then a else nodeHash (a :: b :: zs)

/-- One digest-level merge of the top (rightmost) `k` stack entries. -/
noncomputable def mergeTopD (k : Nat) (stack : List Digest) : List Digest :=
  if stack.length < k then stack
  else stack.take (stack.length - k) ++ [naryMr (stack.drop (stack.length - k))]

theorem mergeTopD_length_lt (k : Nat) (stack : List Digest)
    (hk : 2 ≤ k) (hlen : k < stack.length) :
    (mergeTopD k stack).length < stack.length := by
  unfold mergeTopD
  rw [if_neg (by omega)]
  simp [List.length_take]
  omega

/-- Iterated digest-level merge. -/
noncomputable def mergeTopDN (k : Nat) : Nat → List Digest → List Digest
  | 0, s => s
  | c + 1, s => mergeTopDN k c (mergeTopD k s)

/-- One append at index `idx`: push the cell, run the carry schedule.
    Faithful to the merge loop of `append_leaf`/`append_subtree`
    (`cmt/src/tree.rs`), which merges via `nary_mr`. -/
noncomputable def appendCell (k : Nat) (stack : List Digest) (cell : Digest)
    (idx : Nat) : List Digest :=
  mergeTopDN k (reductionCount k idx) (stack ++ [cell])

noncomputable def buildStackGo (k : Nat) (stack : List Digest) (idx : Nat) :
    List Digest → List Digest
  | [] => stack
  | c :: cs => buildStackGo k (appendCell k stack c idx) (idx + 1) cs

/-- The frontier stack after appending all level-0 `cells` in order. -/
noncomputable def buildStackCells (k : Nat) (cells : List Digest) : List Digest :=
  buildStackGo k [] 0 cells

/-- Canonical root of the perfect k-ary subtree of height `h` over
    `cells[left, left + k^h)`: children leftmost-first, folded with the
    same null-promoting `naryMr` the builder uses. Out-of-range cells
    default to `emptyHash` (irrelevant under the tiling hypothesis). -/
noncomputable def perfectRoot (k : Nat) (cells : List Digest) (left : Nat) :
    Nat → Digest
  | 0 => cells.getD left emptyHash
  | h + 1 =>
      naryMr ((List.range k).map fun j =>
        perfectRoot k cells (left + j * k ^ h) h)

/-! Bridge support: the build distributes over a final cell, `perfectRoot`
    only reads in-range cells, and frontier spans stay within bounds. -/

/-- The tiling start never exceeds its stop. -/
private theorem Tiles_le (k : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop : Nat),
      Tiles k start coords stop → start ≤ stop := by
  intro coords
  induction coords with
  | nil => intro start stop h; exact le_of_eq h
  | cons p rest ih =>
    intro start stop h
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := h
    have := ih (start + k ^ ph) stop htrest
    omega

/-- Each tiled span fits within the stop. -/
theorem Tiles_entry_bound (k : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop : Nat),
      Tiles k start coords stop → ∀ lh ∈ coords, lh.1 + k ^ lh.2 ≤ stop := by
  intro coords
  induction coords with
  | nil => intro start stop _ lh hmem; simp only [List.not_mem_nil] at hmem
  | cons p rest ih =>
    intro start stop htiles lh hmem
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem'
    · have hle := Tiles_le k rest (start + k ^ ph) stop htrest
      show pl + k ^ ph ≤ stop
      omega
    · exact ih (start + k ^ ph) stop htrest lh hmem'

/-- Processing one more cell at the end is one more `appendCell`. -/
private theorem buildStackGo_snoc (k : Nat) :
    ∀ (cs : List Digest) (stack : List Digest) (idx : Nat) (c : Digest),
      buildStackGo k stack idx (cs ++ [c]) =
        appendCell k (buildStackGo k stack idx cs) c (idx + cs.length) := by
  intro cs
  induction cs with
  | nil => intro stack idx c; simp [buildStackGo]
  | cons d ds ih =>
    intro stack idx c
    simp only [List.cons_append, buildStackGo]
    rw [ih (appendCell k stack d idx) (idx + 1) c, List.length_cons,
      show idx + 1 + ds.length = idx + (ds.length + 1) by omega]

/-- `perfectRoot` only reads cells within the subtree span, so appending more
    cells beyond it leaves the root unchanged. -/
theorem perfectRoot_stable (k : Nat) (cells extra : List Digest) :
    ∀ (h left : Nat), left + k ^ h ≤ cells.length →
      perfectRoot k cells left h = perfectRoot k (cells ++ extra) left h := by
  intro h
  induction h with
  | zero =>
    intro left hle
    rw [pow_zero] at hle
    show cells.getD left emptyHash = (cells ++ extra).getD left emptyHash
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
  | succ n ih =>
    intro left hle
    simp only [perfectRoot]
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    apply ih
    have h1 : j * k ^ n + k ^ n = (j + 1) * k ^ n := by ring
    have h2 : (j + 1) * k ^ n ≤ k ^ (n + 1) := by
      calc (j + 1) * k ^ n ≤ k * k ^ n := by gcongr; omega
        _ = k ^ (n + 1) := by rw [pow_succ']
    omega

/-- The trailing `k` coordinates form a perfect k-ary block of equal height —
    the precondition under which a digest merge realizes a `perfectRoot`. -/
def IsBlockTop (k : Nat) (coords : List (Nat × Nat)) : Prop :=
  k ≤ coords.length ∧
    ∃ l h, coords.drop (coords.length - k) = (List.range k).map (fun i => (l + i * k ^ h, h))

/-- **Single-step digest/coordinate simulation.** When the trailing `k` coords
    form a valid block, one digest merge equals the coordinate merge under the
    `perfectRoot` map — because the block's `naryMr` is exactly `perfectRoot`
    of the parent (definitional unfold of `perfectRoot (h+1)`). -/
private theorem mergeTopD_sim (k : Nat) (hk : 1 ≤ k) (cells : List Digest)
    (coords : List (Nat × Nat)) (hblock : IsBlockTop k coords) :
    mergeTopD k (coords.map (fun lh => perfectRoot k cells lh.1 lh.2)) =
      (mergeTopCoords k coords).map (fun lh => perfectRoot k cells lh.1 lh.2) := by
  obtain ⟨hlen, l, h, hdrop⟩ := hblock
  have hnary : naryMr ((coords.drop (coords.length - k)).map
      (fun lh => perfectRoot k cells lh.1 lh.2)) = perfectRoot k cells l (h + 1) := by
    rw [hdrop, List.map_map]
    conv_rhs => rw [perfectRoot]
    apply congrArg (naryMr)
    apply List.map_congr_left
    intro i _
    simp [Function.comp]
  have hhead : (coords.drop (coords.length - k)).head? = some (l, h) := by
    rw [hdrop, List.head?_map]
    have hr : (List.range k).head? = some 0 := by
      rw [show k = (k - 1) + 1 by omega, List.range_succ_eq_map]; rfl
    rw [hr]; simp
  have hLHS : mergeTopD k (coords.map (fun lh => perfectRoot k cells lh.1 lh.2)) =
      (coords.take (coords.length - k)).map (fun lh => perfectRoot k cells lh.1 lh.2) ++
        [perfectRoot k cells l (h + 1)] := by
    unfold mergeTopD
    rw [List.length_map, if_neg (by omega), ← List.map_take, ← List.map_drop, hnary]
  have hRHS : (mergeTopCoords k coords).map (fun lh => perfectRoot k cells lh.1 lh.2) =
      (coords.take (coords.length - k)).map (fun lh => perfectRoot k cells lh.1 lh.2) ++
        [perfectRoot k cells l (h + 1)] := by
    unfold mergeTopCoords
    rw [if_neg (by omega), hhead]
    simp
  rw [hLHS, hRHS]

/-- **Chained simulation.** If every intermediate state has a valid trailing
    block, the iterated digest merge tracks the iterated coordinate merge. -/
private theorem simChain (k : Nat) (hk : 1 ≤ k) (cells : List Digest) :
    ∀ (c : Nat) (coords : List (Nat × Nat)),
      (∀ j < c, IsBlockTop k (mergeTopCoordsN k j coords)) →
      mergeTopDN k c (coords.map (fun lh => perfectRoot k cells lh.1 lh.2)) =
        (mergeTopCoordsN k c coords).map (fun lh => perfectRoot k cells lh.1 lh.2) := by
  intro c
  induction c with
  | zero => intro coords _; rfl
  | succ c ih =>
    intro coords hvalid
    have hval' : ∀ j < c, IsBlockTop k (mergeTopCoordsN k j (mergeTopCoords k coords)) :=
      fun j hj => hvalid (j + 1) (by omega)
    show mergeTopDN k c (mergeTopD k (coords.map (fun lh => perfectRoot k cells lh.1 lh.2)))
       = (mergeTopCoordsN k (c + 1) coords).map (fun lh => perfectRoot k cells lh.1 lh.2)
    rw [mergeTopD_sim k hk cells coords (hvalid 0 (by omega)),
      ih (mergeTopCoords k coords) hval']
    rfl

/-- Scaling a list one level up preserves a valid trailing block (with the
    block lifted one level). -/
private theorem IsBlockTop_scale (k : Nat) (Z : List (Nat × Nat)) (hZ : IsBlockTop k Z) :
    IsBlockTop k (Z.map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1))) := by
  obtain ⟨hlen, l, h, hdrop⟩ := hZ
  refine ⟨by rw [List.length_map]; exact hlen, l * k, h + 1, ?_⟩
  rw [List.length_map, ← List.map_drop, hdrop, List.map_map]
  apply List.map_congr_left
  intro i _
  show ((l + i * k ^ h) * k, h + 1) = (l * k + i * k ^ (h + 1), h + 1)
  rw [Prod.mk.injEq, pow_succ]
  exact ⟨by ring, rfl⟩

/-- **Every carry merge is a valid block.** During the append of leaf `len`,
    each of the `reductionCount k len` merges acts on a perfect k-ary block.
    Proved by the same base-`k` division induction as the carry schedule:
    the first merge consumes the completed bottom run; the rest are the
    carries of `(len+1)/k - 1` lifted one level. -/
private theorem validCarry (k : Nat) (hk : 2 ≤ k) :
    ∀ len, ∀ j < reductionCount k len,
      IsBlockTop k (mergeTopCoordsN k j (frontierForSizeT k len ++ [(len, 0)])) := by
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intro j hj
    by_cases hmod0 : (len + 1) % k = 0
    · have hdvd : k ∣ (len + 1) := Nat.dvd_of_mod_eq_zero hmod0
      have hkle : k ≤ len + 1 := Nat.le_of_dvd (by omega) hdvd
      set m := (len + 1) / k with hm
      have hmk : m * k = len + 1 := by rw [hm]; exact Nat.div_mul_cancel hdvd
      have hmpos : 0 < m := by rw [hm]; exact Nat.div_pos hkle (by omega)
      have hmlt : m < len + 1 := by rw [hm]; exact Nat.div_lt_self (by omega) (by omega)
      have hmlt' : m - 1 < len := by omega
      have hrceq : reductionCount k len = 1 + reductionCount k (m - 1) := by
        unfold reductionCount
        conv_lhs => rw [reductionCountGo]
        rw [dif_pos ⟨by omega, by omega, hmod0⟩]
        congr 1
        rw [← hm]; congr 1; omega
      have hn_eq : len = (m - 1) * k + (k - 1) := by rw [Nat.sub_one_mul]; omega
      have hrange : List.range k = List.range (k - 1) ++ [k - 1] := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega]
        rw [List.range_succ]
      have hfn : frontierForSizeT k len =
          (frontierForSizeT k (m - 1)).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) ++
          (List.range (k - 1)).map (fun i => ((m - 1) * k + i, 0)) := by
        rw [hn_eq]; exact frontier_divstep k hk (m - 1) (k - 1) (by omega)
      have hX : frontierForSizeT k len ++ [(len, 0)] =
          (frontierForSizeT k (m - 1)).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) ++
          (List.range k).map (fun i => ((m - 1) * k + i, 0)) := by
        rw [hfn, List.append_assoc]
        congr 1
        rw [hrange, List.map_append]
        congr 1
        simp [hn_eq]
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        rw [show mergeTopCoordsN k 0 (frontierForSizeT k len ++ [(len, 0)])
              = frontierForSizeT k len ++ [(len, 0)] from rfl, hX]
        refine ⟨?_, (m - 1) * k, 0, ?_⟩
        · simp only [List.length_append, List.length_map, List.length_range]; omega
        · have hdroplen :
              ((frontierForSizeT k (m - 1)).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) ++
                (List.range k).map (fun i => ((m - 1) * k + i, 0))).length - k =
              ((frontierForSizeT k (m - 1)).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1))).length := by
            simp only [List.length_append, List.length_map, List.length_range]; omega
          rw [hdroplen, List.drop_left]
          apply List.map_congr_left
          intro i _
          rw [pow_zero, Nat.mul_one]
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hj'lt : j' < reductionCount k (m - 1) := by rw [hrceq] at hj; omega
        rw [show mergeTopCoordsN k (j' + 1) (frontierForSizeT k len ++ [(len, 0)])
              = mergeTopCoordsN k j'
                  (mergeTopCoords k (frontierForSizeT k len ++ [(len, 0)])) from rfl,
          hX, mergeTopCoords_group k (by omega)
            ((frontierForSizeT k (m - 1)).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1))) ((m - 1) * k),
          show (frontierForSizeT k (m - 1)).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) ++
                [((m - 1) * k, 1)]
              = (frontierForSizeT k (m - 1) ++ [(m - 1, 0)]).map (fun lh : Nat × Nat => (lh.1 * k, lh.2 + 1)) from by
            rw [List.map_append]; simp,
          mergeTopCoordsN_scale]
        exact IsBlockTop_scale k _ (ih (m - 1) hmlt' j' hj'lt)
    · have h0 : reductionCount k len = 0 := by
        unfold reductionCount
        rw [reductionCountGo, dif_neg (by rintro ⟨_, _, h⟩; exact hmod0 h)]
      omega

/-- **K-ary bridge lemma.** The frontier stack machine computes exactly the
    perfect-subtree roots of the frontier decomposition. This is the k-ary
    generalization of `bridge_lemma` (`Bridge.lean`), which covers only
    binary nodes via the degenerate linear policy.

    *Strategy:* strengthen to an invariant over `buildStackGo` ("after `n`
    appends the stack is the mapped frontier of size `n`") and induct using
    `frontier_append_consistent` for the coordinate evolution plus a
    digest/coordinate simulation lemma: `mergeTopD` tracks
    `mergeTopCoords` when the stack is the mapped frontier (the merged
    top-k coords are same-height consecutive blocks, so their `naryMr`
    is `perfectRoot` of the parent — definitional unfold of
    `perfectRoot (h+1)`). Template: `buildStack_invariant` in
    `Bridge.lean`. -/
theorem kary_bridge (k : Nat) (hk : 2 ≤ k) (cells : List Digest) :
    buildStackCells k cells =
      (frontierForSizeT k cells.length).map
        (fun lh => perfectRoot k cells lh.1 lh.2) := by
  induction cells using List.reverseRecOn with
  | nil =>
    rw [buildStackCells, frontierForSizeT, frontierGo]
    simp [buildStackGo]
  | append_singleton cs c ih =>
    have hlenc : (cs ++ [c]).length = cs.length + 1 := by simp
    rw [buildStackCells, buildStackGo_snoc, Nat.zero_add,
      show buildStackGo k [] 0 cs = buildStackCells k cs from rfl, ih, appendCell]
    have hstab :
        (frontierForSizeT k cs.length).map (fun lh : Nat × Nat => perfectRoot k cs lh.1 lh.2)
        = (frontierForSizeT k cs.length).map
            (fun lh : Nat × Nat => perfectRoot k (cs ++ [c]) lh.1 lh.2) := by
      apply List.map_congr_left
      intro lh hlh
      exact perfectRoot_stable k cs [c] lh.2 lh.1
        (Tiles_entry_bound k (frontierForSizeT k cs.length) 0 cs.length
          (frontier_tiles k cs.length hk) lh hlh)
    have hc : perfectRoot k (cs ++ [c]) cs.length 0 = c := by
      show (cs ++ [c]).getD cs.length emptyHash = c
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        show cs.length - cs.length = 0 from by omega]
      rfl
    have hmerge :
        (frontierForSizeT k cs.length).map (fun lh : Nat × Nat => perfectRoot k cs lh.1 lh.2) ++ [c]
        = (frontierForSizeT k cs.length ++ [(cs.length, 0)]).map
            (fun lh : Nat × Nat => perfectRoot k (cs ++ [c]) lh.1 lh.2) := by
      rw [hstab, List.map_append, List.map_cons, List.map_nil, hc]
    rw [hmerge,
      simChain k (by omega) (cs ++ [c]) (reductionCount k cs.length)
        (frontierForSizeT k cs.length ++ [(cs.length, 0)]) (validCarry k hk cs.length),
      ← frontier_append_consistent k cs.length hk, hlenc]

/-- Fold the frontier stack to the spine root: merge the rightmost `k` while
    more than `k` remain, then one final `naryMr` (which also covers the
    empty → `emptyHash` and singleton-promotion cases). Mirrors
    `compute_root_from_state` (`cmt/src/tree.rs`) and the fold described in
    `topology.rs` module docs. -/
noncomputable def foldFrontierRoot (k : Nat) (stack : List Digest) : Digest :=
  if h : k < 2 ∨ stack.length ≤ k then naryMr stack
  else foldFrontierRoot k (mergeTopD k stack)
termination_by stack.length
decreasing_by
  push_neg at h
  exact mergeTopD_length_lt k stack (by omega) h.2

/-- The per-algorithm raw root over level-0 `cells` (flat: leaf hashes;
    subtree kind: stored subtree roots). -/
noncomputable def karyRoot (k : Nat) (cells : List Digest) : Digest :=
  foldFrontierRoot k (buildStackCells k cells)

/-! ## Layer 3 — the verifier model and its theorems -/

/-- `(position, sibling count)` of a proof step — the shape the skeleton pins. -/
def stepShape (s : ProofStep) : Nat × Nat := (s.position, s.siblings.length)

/-- `verify_inclusion_path_structure`, faithfully: the skeleton must exist,
    the path must be at least as long, and the trailing `skel.length` steps
    must match it shape-for-shape. The leading `d` steps (within-subtree
    prefix) are unconstrained here — they are existentially bound by
    soundness, never pinned. -/
def StructureOK (k index treeSize : Nat) (path : List ProofStep) : Prop :=
  ∃ skel, inclusionSkeleton k treeSize index = some skel ∧
    skel.length ≤ path.length ∧
    (path.drop (path.length - skel.length)).map stepShape = skel

/-- Per-step well-formedness enforced by `reconstruct_inclusion_root`:
    zero-sibling (promoted) steps rejected — canonical encoding — and the
    insert position within bounds. -/
def WellFormedSteps (path : List ProofStep) : Prop :=
  ∀ s ∈ path, s.siblings ≠ [] ∧ s.position ≤ s.siblings.length

/-- One verifier fold step: insert the running digest among the siblings at
    `position`, hash with null-promoting `naryMr`. With ≥ 1 sibling the
    singleton-promotion arm of `naryMr` is dead — but the *null*-promotion
    arm is live, which `foldCanonical`/`applyStep` (plain `nodeHash`) gets
    wrong. -/
noncomputable def applyStepN (cur : Digest) (s : ProofStep) : Digest :=
  naryMr (insertAt s.position cur s.siblings)

/-- The verifier's root reconstruction (`reconstruct_inclusion_root` fold). -/
noncomputable def foldNary (leaf : Digest) (path : List ProofStep) : Digest :=
  path.foldl (applyStepN) leaf

/-- The accept relation of `verify_inclusion`, minus DoS bounds:
    range guards, skeleton pinning, canonical well-formedness, and the
    fold reaching `root`. -/
def AcceptsKary (k : Nat) (leaf : Digest) (index treeSize : Nat)
    (root : Digest) (path : List ProofStep) : Prop :=
  2 ≤ k ∧ 0 < treeSize ∧ index < treeSize ∧
  StructureOK k index treeSize path ∧
  WellFormedSteps path ∧
  foldNary leaf path = root

/-- A same-value collapse value colliding with a genuine node hash: a not-all-
    equal list of ≥ 2 children whose `nodeHash` equals some value `v` that an
    all-equal-to-`v` list collapses to. Untagged `nodeHash = H(concat)` makes
    this an `H` collision unless the child bytes concatenate to the `v`-run
    preimage; `digestToBytes` is unconstrained, so it is surfaced as an explicit
    assumption rather than argued away. The all-null instance (`v = nullDigest`)
    is the dominant case in a sparse log. -/
def CollapseAmbiguity : Prop :=
  ∃ (cs : List Digest) (v : Digest), 2 ≤ cs.length ∧ ¬(∀ c ∈ cs, c = v) ∧
    nodeHash cs = v

/-- **Fixed-arity injectivity of `naryMr`.** Same-length child lists of
    length ≥ 2 with equal `naryMr` are equal — or a hash assumption broke.
    The general-collapse analysis: two all-equal lists of equal length that
    collapse to the same value are *elementwise* equal to it, hence equal (this
    is why same-length matters: all-equal lists of different lengths collide by
    design, which the skeleton's arity pinning excludes); one collapsing and one
    hashing is `CollapseAmbiguity`; both hashing reduces to `NodeHashCollision`.
    *Strategy:* case on the two `if`s; the collapse/collapse case is `List.ext`
    via length + pointwise equality to the shared (equal) value. -/
theorem naryMr_inj_of_length (xs ys : List Digest)
    (hlen : xs.length = ys.length) (h2 : 2 ≤ xs.length)
    (heq : naryMr xs = naryMr ys)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    xs = ys := by
  have hys2 : 2 ≤ ys.length := hlen ▸ h2
  -- Length ≥ 2 forces both lists into the catch-all arm of `naryMr`.
  obtain ⟨a, b, xr, rfl⟩ : ∃ a b xr, xs = a :: b :: xr := by
    rcases xs with _ | ⟨a, _ | ⟨b, xr⟩⟩
    · simp only [List.length_nil] at h2; omega
    · simp only [List.length_cons, List.length_nil] at h2; omega
    · exact ⟨a, b, xr, rfl⟩
  obtain ⟨c, d, yr, rfl⟩ : ∃ c d yr, ys = c :: d :: yr := by
    rcases ys with _ | ⟨c, _ | ⟨d, yr⟩⟩
    · simp only [List.length_nil] at hys2; omega
    · simp only [List.length_cons, List.length_nil] at hys2; omega
    · exact ⟨c, d, yr, rfl⟩
  simp only [naryMr] at heq
  by_cases hxn : ∀ z ∈ a :: b :: xr, z = a
  · by_cases hyn : ∀ z ∈ c :: d :: yr, z = c
    · -- Both collapse: `naryMr = a` and `= c`, so `a = c`; both lists are all-`a`
      -- of the same length ⇒ elementwise equal.
      rw [if_pos hxn, if_pos hyn] at heq
      apply List.ext_getElem hlen
      intro i h1 h2'
      rw [hxn _ (List.getElem_mem h1), hyn _ (List.getElem_mem h2'), heq]
    · -- `xs` collapses to `a`, `ys` hashes ⇒ `nodeHash ys = a`: CollapseAmbiguity
      -- with value `a`. `ys` is not all-`a`: were it, its head `c = a`, so its own
      -- collapse guard (`∀ z = c`) would hold, contradicting `hyn`.
      rw [if_pos hxn, if_neg hyn] at heq
      have hya : ¬ ∀ z ∈ c :: d :: yr, z = a := by
        intro hall
        exact hyn (fun z hz => by rw [hall z hz, hall c (by simp)])
      exact absurd ⟨c :: d :: yr, a, hys2, hya, heq.symm⟩ hN
  · by_cases hyn : ∀ z ∈ c :: d :: yr, z = c
    · -- symmetric: `ys` collapses to `c`, `xs` hashes ⇒ `nodeHash xs = c`.
      rw [if_neg hxn, if_pos hyn] at heq
      have hxc : ¬ ∀ z ∈ a :: b :: xr, z = c := by
        intro hall
        exact hxn (fun z hz => by rw [hall z hz, hall a (by simp)])
      exact absurd ⟨a :: b :: xr, c, h2, hxc, heq⟩ hN
    · rw [if_neg hxn, if_neg hyn] at heq
      by_contra hne
      exact hH ⟨a :: b :: xr, c :: d :: yr, hne, heq⟩

/-- `insertAt` adds exactly one element. -/
private theorem insertAt_length {α : Type} (n : Nat) (x : α) (l : List α) :
    (insertAt n x l).length = l.length + 1 := by
  induction l generalizing n with
  | nil => simp [insertAt]
  | cons y ys ih =>
    cases n with
    | zero => simp [insertAt]
    | succ m => simp [insertAt, ih]

/-- Fold-append: the running digest after the prefix, then one step. -/
private theorem foldNary_append_last (a : Digest)
    (p' : List ProofStep) (s : ProofStep) :
    foldNary a (p' ++ [s]) = applyStepN (foldNary a p') s := by
  simp only [foldNary, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem foldNary_unique_aux 
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    ∀ (n : Nat) (a b : Digest) (p q : List ProofStep),
      p.length = n → q.length = n →
      p.map stepShape = q.map stepShape →
      WellFormedSteps p → WellFormedSteps q →
      foldNary a p = foldNary b q →
      a = b ∧ p = q := by
  intro n
  induction n with
  | zero =>
    intro a b p q hp hq _ _ _ heq
    have hpe : p = [] := List.eq_nil_of_length_eq_zero hp
    have hqe : q = [] := List.eq_nil_of_length_eq_zero hq
    subst hpe; subst hqe
    simp only [foldNary, List.foldl_nil] at heq
    exact ⟨heq, rfl⟩
  | succ m ih =>
    intro a b p q hp hq hshape hwfp hwfq heq
    obtain ⟨p', s₁, hp_eq, hp'_len⟩ := list_decomp_last p hp
    obtain ⟨q', s₂, hq_eq, hq'_len⟩ := list_decomp_last q hq
    subst hp_eq; subst hq_eq
    -- Split the shape equality into prefix + last step.
    rw [List.map_append, List.map_append] at hshape
    have hlenmap : (p'.map stepShape).length = (q'.map stepShape).length := by
      simp only [List.length_map, hp'_len, hq'_len]
    obtain ⟨hshape', hslast⟩ := List.append_inj hshape hlenmap
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hslast
    have hsstep : stepShape s₁ = stepShape s₂ := hslast
    simp only [stepShape, Prod.mk.injEq] at hsstep
    obtain ⟨hpos, hsiblen⟩ := hsstep
    -- Well-formedness of the last steps and of the prefixes.
    have hwf_s1 := hwfp s₁ (List.mem_append.mpr (Or.inr (by simp)))
    have hwfp' : WellFormedSteps p' := fun s hs => hwfp s (List.mem_append.mpr (Or.inl hs))
    have hwfq' : WellFormedSteps q' := fun s hs => hwfq s (List.mem_append.mpr (Or.inl hs))
    -- Peel the last fold step and invert it.
    rw [foldNary_append_last, foldNary_append_last] at heq
    simp only [applyStepN] at heq
    have hxs2 : 2 ≤ (insertAt s₁.position (foldNary a p') s₁.siblings).length := by
      rw [insertAt_length]
      have hne : s₁.siblings.length ≠ 0 := fun h0 =>
        hwf_s1.1 (List.eq_nil_of_length_eq_zero h0)
      omega
    have hxylen :
        (insertAt s₁.position (foldNary a p') s₁.siblings).length =
          (insertAt s₂.position (foldNary b q') s₂.siblings).length := by
      rw [insertAt_length, insertAt_length, hsiblen]
    have hnode := naryMr_inj_of_length _ _ hxylen hxs2 heq hH hN
    rw [hpos] at hnode
    obtain ⟨hfold, hsib⟩ :=
      insertAt_injective s₂.position (foldNary a p') (foldNary b q')
        s₁.siblings s₂.siblings hnode
    obtain ⟨hab, hpq⟩ := ih a b p' q' hp'_len hq'_len hshape' hwfp' hwfq' hfold
    refine ⟨hab, ?_⟩
    have hstep : s₁ = s₂ := by
      cases s₁ with | mk sib1 pos1 =>
      cases s₂ with | mk sib2 pos2 =>
      simp only [ProofStep.mk.injEq]
      exact ⟨hsib, hpos⟩
    rw [hpq, hstep]

/-- **Shape-pinned fold uniqueness — the soundness engine.** Two well-formed
    paths of identical shape folding to the same digest coincide entirely,
    including their starting digests. The k-ary, null-promoting analog of
    `foldCanonical_unique_of_len` (Spine.lean), whose induction structure
    (back-decomposition of both paths, `insertAt_injective` per step) is
    the template; each step applies `naryMr_inj_of_length`, with
    `insertAt` preserving the pinned length
    (`(insertAt p c s).length = s.length + 1 ≥ 2` from `WellFormedSteps`). -/
theorem foldNary_unique_of_shape (a b : Digest)
    (p q : List ProofStep)
    (hshape : p.map stepShape = q.map stepShape)
    (hwfp : WellFormedSteps p) (hwfq : WellFormedSteps q)
    (heq : foldNary a p = foldNary b q)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    a = b ∧ p = q := by
  have hlenpq : p.length = q.length := by
    have := congrArg List.length hshape
    simpa using this
  exact foldNary_unique_aux hH hN p.length a b p q rfl hlenpq.symm
    hshape hwfp hwfq heq

/-! ### The honest prover -/

/-- Honest within-subtree digit path for offset `offset` in the frontier
    subtree at `(left, h)`: at level `j` the path node sits at digit
    `(offset / k^j) % k` among the `k` children of the level-`j+1` block;
    siblings are the other `k - 1` perfect roots, in child order. -/
noncomputable def honestDigitPath (k : Nat) (cells : List Digest)
    (left offset h : Nat) : List ProofStep :=
  (List.range h).map fun j =>
    { position := offset / k ^ j % k,
      siblings := ((List.range k).filter (fun i => i != offset / k ^ j % k)).map
        fun i => perfectRoot k cells (left + (offset / k ^ (j + 1) * k + i) * k ^ j) j }

/-- Honest grouping path: replay the frontier fold, emitting a step (with
    the other merge participants as siblings, path node erased) whenever the
    tracked slot is inside the merged window. Same recursion as
    `groupingSteps`, carrying digests. -/
noncomputable def honestGroupPath (k : Nat) (stack : List Digest)
    (fIdx : Nat) : List ProofStep :=
  if h : k < 2 ∨ stack.length ≤ k then
    if 1 < stack.length then
      [{ position := fIdx, siblings := stack.eraseIdx fIdx }]
    else []
  else
    if fIdx ≥ stack.length - k then
      { position := fIdx - (stack.length - k),
        siblings := (stack.drop (stack.length - k)).eraseIdx
          (fIdx - (stack.length - k)) } ::
        honestGroupPath k (mergeTopD k stack) (stack.length - k)
    else
      honestGroupPath k (mergeTopD k stack) fIdx
termination_by stack.length
decreasing_by
  all_goals (push_neg at h; exact mergeTopD_length_lt k stack (by omega) h.2)

/-- The honest inclusion path for log position `index`: digit steps inside
    its frontier subtree, then grouping steps to the spine root. Mirrors
    proof generation (which derives the same skeleton from
    `inclusion_skeleton`). -/
noncomputable def honestInclusionPath (k : Nat) (cells : List Digest)
    (index : Nat) : List ProofStep :=
  match findFrontier k index (frontierForSizeT k cells.length) 0 with
  | none => []
  | some (fIdx, l, h) =>
      honestDigitPath k cells l (index - l) h ++
        honestGroupPath k (buildStackCells k cells) fIdx

/-! Honest-prover shape support. -/

/-- Removing the single matching element from `range k` leaves `k - 1`. -/
private theorem filter_ne_range_length (k p : Nat) (hp : p < k) :
    ((List.range k).filter (fun i => i != p)).length = k - 1 := by
  induction k with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append]
    rcases Nat.lt_or_ge p n with hpn | hpn
    · rw [ih hpn]
      have hkeep : (([n] : List Nat).filter (fun i => i != p)).length = 1 := by
        have hb : (n != p) = true := by simp [bne_iff_ne]; omega
        simp [List.filter_cons, hb]
      omega
    · have hpeq : p = n := by omega
      subst hpeq
      have hr : ((List.range p).filter (fun i => i != p)).length = p := by
        have hself : (List.range p).filter (fun i => i != p) = List.range p := by
          apply List.filter_eq_self.mpr
          intro a ha
          rw [List.mem_range] at ha
          simp [bne_iff_ne]; omega
        rw [hself, List.length_range]
      have hdrop : (([p] : List Nat).filter (fun i => i != p)).length = 0 := by
        simp [List.filter_cons]
      omega

/-- `digitSteps` as a closed-form map over levels. -/
theorem digitSteps_eq_map (k : Nat) :
    ∀ (h offset : Nat),
      digitSteps k offset h = (List.range h).map (fun j => (offset / k ^ j % k, k - 1)) := by
  intro h
  induction h with
  | zero => intro offset; rfl
  | succ n ih =>
    intro offset
    rw [digitSteps, List.range_succ_eq_map, List.map_cons, List.map_map, ih (offset / k)]
    congr 1
    · simp
    · apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      rw [Nat.div_div_eq_div_mul, ← pow_succ']

/-- Exact length after a merge (when the stack is long enough). -/
private theorem mergeTopD_length (k : Nat) (stack : List Digest) (h : ¬ stack.length < k) :
    (mergeTopD k stack).length = stack.length - k + 1 := by
  unfold mergeTopD
  rw [if_neg h]
  simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]
  omega

/-- The honest grouping path realizes the mapped grouping skeleton. -/
private theorem honestGroupPath_shape (k : Nat) (hk : 2 ≤ k) :
    ∀ (n : Nat) (stack : List Digest) (fIdx : Nat),
      stack.length = n → fIdx < stack.length →
      (honestGroupPath k stack fIdx).map stepShape
        = (groupingSteps k stack.length fIdx).map (fun pc => (pc.1, pc.2 - 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro stack fIdx hn hlt
    by_cases hbase : k < 2 ∨ stack.length ≤ k
    · rw [honestGroupPath, dif_pos hbase, groupingSteps, dif_pos hbase]
      by_cases h1 : 1 < stack.length
      · rw [if_pos h1, if_pos h1]
        simp only [List.map_cons, List.map_nil, stepShape, List.length_eraseIdx_of_lt hlt]
      · simp only [if_neg h1, List.map_nil]
    · rw [honestGroupPath, dif_neg hbase, groupingSteps, dif_neg hbase]
      push_neg at hbase
      obtain ⟨_, hgt⟩ := hbase
      have hml : (mergeTopD k stack).length = stack.length - k + 1 :=
        mergeTopD_length k stack (by omega)
      by_cases hge : fIdx ≥ stack.length - k
      · rw [if_pos hge, if_pos hge, List.map_cons, List.map_cons]
        refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
        · simp only [stepShape]
          have hdl : (stack.drop (stack.length - k)).length = k := by
            rw [List.length_drop]; omega
          rw [List.length_eraseIdx_of_lt (by rw [hdl]; omega), hdl]
        · rw [← hml]
          exact ih (mergeTopD k stack).length (by omega) (mergeTopD k stack)
            (stack.length - k) rfl (by omega)
      · rw [if_neg hge, if_neg hge, ← hml]
        exact ih (mergeTopD k stack).length (by omega) (mergeTopD k stack)
          fIdx rfl (by omega)

/-- A tiled coordinate covering `index` is found by `findFrontier`. -/
theorem findFrontier_cover (k index : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop c : Nat),
      Tiles k start coords stop → start ≤ index → index < stop →
      ∃ fIdx l h, findFrontier k index coords c = some (fIdx, l, h) := by
  intro coords
  induction coords with
  | nil => intro start stop c htiles hs hlt; simp only [Tiles] at htiles; omega
  | cons p rest ih =>
    intro start stop c htiles hs hlt
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    rw [findFrontier]
    by_cases hcond : pl ≤ index ∧ index < pl + k ^ ph
    · rw [if_pos hcond]; exact ⟨c, pl, ph, rfl⟩
    · rw [if_neg hcond]
      push_neg at hcond
      have hpli : pl + k ^ ph ≤ index := hcond (by omega)
      exact ih (start + k ^ ph) stop (c + 1) htrest (by omega) hlt

/-- The honest path realizes the skeleton exactly (no prefix: `d = 0` at the
    cell level) and is well-formed. Well-formedness is derived from the shape
    via `skeleton_no_promoted` rather than re-proven. -/
theorem honest_path_shape (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (index : Nat) (hidx : index < cells.length) :
    (∃ skel, inclusionSkeleton k cells.length index = some skel ∧
      (honestInclusionPath k cells index).map stepShape = skel) ∧
    WellFormedSteps (honestInclusionPath k cells index) := by
  set fr := frontierForSizeT k cells.length with hfr
  obtain ⟨fIdx, l, h, hff⟩ := findFrontier_cover k index fr 0 cells.length 0
    (by rw [hfr]; exact frontier_tiles k cells.length hk) (by omega) hidx
  have hbuild : (buildStackCells k cells).length = fr.length := by
    rw [hfr, kary_bridge k hk cells, List.length_map]
  have hfidxlt : fIdx < fr.length := by
    simpa using findFrontier_slot_lt k index fr 0 fIdx l h hff
  have hskel : inclusionSkeleton k cells.length index =
      some (digitSteps k (index - l) h ++
        (groupingSteps k fr.length fIdx).map (fun pc => (pc.1, pc.2 - 1))) := by
    rw [inclusionSkeleton, if_neg (by omega), ← hfr, hff]
  have hpath : honestInclusionPath k cells index =
      honestDigitPath k cells l (index - l) h ++
        honestGroupPath k (buildStackCells k cells) fIdx := by
    rw [honestInclusionPath, ← hfr, hff]
  have hshape : (honestInclusionPath k cells index).map stepShape =
      digitSteps k (index - l) h ++
        (groupingSteps k fr.length fIdx).map (fun pc => (pc.1, pc.2 - 1)) := by
    rw [hpath, List.map_append]
    congr 1
    · rw [honestDigitPath, List.map_map, digitSteps_eq_map]
      apply List.map_congr_left
      intro j _
      simp only [Function.comp, stepShape, List.length_map]
      rw [filter_ne_range_length k ((index - l) / k ^ j % k) (Nat.mod_lt _ (by omega))]
    · rw [honestGroupPath_shape k hk (buildStackCells k cells).length
            (buildStackCells k cells) fIdx rfl (by rw [hbuild]; exact hfidxlt), hbuild]
  refine ⟨⟨_, hskel, hshape⟩, ?_⟩
  intro s hs
  have hmem : stepShape s ∈ digitSteps k (index - l) h ++
      (groupingSteps k fr.length fIdx).map (fun pc => (pc.1, pc.2 - 1)) := by
    rw [← hshape]; exact List.mem_map_of_mem hs
  obtain ⟨h1, h2⟩ := skeleton_no_promoted k cells.length index _ hskel (stepShape s) hmem
  simp only [stepShape] at h1 h2
  refine ⟨fun hnil => ?_, h2⟩
  rw [hnil] at h1
  simp at h1

/-! Honest-prover fold support: reassembling an erased element. -/

private theorem map_eraseIdx {α β} (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.eraseIdx i).map f = (l.map f).eraseIdx i := by
  intro l
  induction l with
  | nil => intro i; rfl
  | cons x xs ih =>
    intro i
    cases i with
    | zero => rfl
    | succ m => simp only [List.eraseIdx_cons_succ, List.map_cons, ih]

private theorem filter_ne_range_eq_eraseIdx (k p : Nat) (hp : p < k) :
    (List.range k).filter (fun i => i != p) = (List.range k).eraseIdx p := by
  induction k with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_or_ge p n with hpn | hpn
    · rw [ih hpn, List.eraseIdx_append_of_lt_length (by rw [List.length_range]; exact hpn)]
      have hb : (n != p) = true := by simp [bne_iff_ne]; omega
      simp [List.filter_cons, hb]
    · have hpeq : p = n := by omega
      subst hpeq
      have hf1 : (List.range p).filter (fun i => i != p) = List.range p := by
        apply List.filter_eq_self.mpr
        intro a ha; rw [List.mem_range] at ha; simp [bne_iff_ne]; omega
      rw [hf1, List.eraseIdx_append_of_length_le (by rw [List.length_range])]
      simp [List.filter_cons]

private theorem insertAt_eraseIdx {α} (d : α) :
    ∀ (l : List α) (n : Nat), n < l.length →
      insertAt n (l.getD n d) (l.eraseIdx n) = l := by
  intro l
  induction l with
  | nil => intro n h; simp at h
  | cons x xs ih =>
    intro n hn
    cases n with
    | zero =>
      simp only [List.getD_cons_zero, List.eraseIdx_cons_zero]
      cases xs <;> rfl
    | succ m =>
      simp only [List.eraseIdx_cons_succ, List.getD_cons_succ]
      show x :: insertAt m (xs.getD m d) (xs.eraseIdx m) = x :: xs
      rw [ih m (by simp only [List.length_cons] at hn; omega)]

private theorem insertAt_filter_range {α} [Inhabited α] (φ : Nat → α) (k p : Nat)
    (hp : p < k) :
    insertAt p (φ p) (((List.range k).filter (fun i => i != p)).map φ) =
      (List.range k).map φ := by
  rw [filter_ne_range_eq_eraseIdx k p hp, map_eraseIdx]
  have hget : ((List.range k).map φ).getD p default = φ p := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp]; rfl
  rw [← hget]
  exact insertAt_eraseIdx default ((List.range k).map φ) p
    (by rw [List.length_map, List.length_range]; exact hp)

/-- The digit path folds the leaf up to its frontier-subtree root. Stated
    generally over `offset` (the conclusion rounds `offset` down to a multiple
    of `k^h`); the in-range use has `offset < k^h`, giving `perfectRoot left h`. -/
theorem digitFold (k : Nat) (hk : 2 ≤ k) (cells : List Digest) (left : Nat) :
    ∀ (h offset : Nat),
      foldNary (cells.getD (left + offset) emptyHash)
        (honestDigitPath k cells left offset h)
        = perfectRoot k cells (left + offset / k ^ h * k ^ h) h := by
  intro h
  induction h with
  | zero =>
    intro offset
    simp [honestDigitPath, foldNary, perfectRoot]
  | succ n ih =>
    intro offset
    have hsplit : honestDigitPath k cells left offset (n + 1)
        = honestDigitPath k cells left offset n ++
          [{ position := offset / k ^ n % k,
             siblings := ((List.range k).filter (fun i => i != offset / k ^ n % k)).map
               fun i => perfectRoot k cells (left + (offset / k ^ (n + 1) * k + i) * k ^ n) n }] := by
      rw [honestDigitPath, honestDigitPath, List.range_succ, List.map_append, List.map_cons,
        List.map_nil]
    rw [hsplit, foldNary_append_last, ih]
    simp only [applyStepN]
    set φ := fun i => perfectRoot k cells (left + offset / k ^ (n + 1) * k ^ (n + 1) + i * k ^ n) n
      with hφ
    have hp : offset / k ^ n % k < k := Nat.mod_lt _ (by omega)
    have hsib : ((List.range k).filter (fun i => i != offset / k ^ n % k)).map
                  (fun i => perfectRoot k cells (left + (offset / k ^ (n + 1) * k + i) * k ^ n) n)
              = ((List.range k).filter (fun i => i != offset / k ^ n % k)).map φ := by
      apply List.map_congr_left
      intro i _
      rw [hφ]
      congr 1
      rw [show k ^ (n + 1) = k ^ n * k from pow_succ k n]
      ring
    have hcur : perfectRoot k cells (left + offset / k ^ n * k ^ n) n
              = φ (offset / k ^ n % k) := by
      have hpow : k ^ (n + 1) = k ^ n * k := pow_succ k n
      have hdd : offset / k ^ (n + 1) = offset / k ^ n / k := by rw [hpow, Nat.div_div_eq_div_mul]
      have hidx : left + offset / k ^ n * k ^ n
                = left + offset / k ^ (n + 1) * k ^ (n + 1) + offset / k ^ n % k * k ^ n := by
        rw [hdd, hpow]
        conv_lhs => rw [← Nat.div_add_mod (offset / k ^ n) k]
        ring
      rw [hφ, hidx]
    rw [hsib, hcur, insertAt_filter_range φ k (offset / k ^ n % k) hp]
    conv_rhs => rw [perfectRoot]

/-- The honest grouping path folds the tracked entry through the frontier
    merges to the spine root. -/
private theorem honestGroupPath_folds (k : Nat) (hk : 2 ≤ k) :
    ∀ (n : Nat) (stack : List Digest) (fIdx : Nat),
      stack.length = n → fIdx < stack.length →
      foldNary (stack.getD fIdx emptyHash) (honestGroupPath k stack fIdx)
        = foldFrontierRoot k stack := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro stack fIdx hn hlt
    by_cases hbase : k < 2 ∨ stack.length ≤ k
    · rw [honestGroupPath, dif_pos hbase, foldFrontierRoot, dif_pos hbase]
      by_cases h1 : 1 < stack.length
      · rw [if_pos h1, foldNary, List.foldl_cons, List.foldl_nil, applyStepN,
          insertAt_eraseIdx emptyHash stack fIdx hlt]
      · rw [if_neg h1, foldNary, List.foldl_nil]
        have hlen1 : stack.length = 1 := by omega
        have hf0 : fIdx = 0 := by omega
        obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen1
        subst hf0
        simp [naryMr]
    · rw [honestGroupPath, dif_neg hbase, foldFrontierRoot, dif_neg hbase]
      push_neg at hbase
      obtain ⟨_, hgt⟩ := hbase
      have hml : (mergeTopD k stack).length = stack.length - k + 1 :=
        mergeTopD_length k stack (by omega)
      have hdroplen : (stack.drop (stack.length - k)).length = k := by
        rw [List.length_drop]; omega
      by_cases hge : fIdx ≥ stack.length - k
      · rw [if_pos hge, foldNary, List.foldl_cons, applyStepN]
        have hstart : stack.getD fIdx emptyHash
            = (stack.drop (stack.length - k)).getD (fIdx - (stack.length - k)) emptyHash := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_drop,
            show (stack.length - k) + (fIdx - (stack.length - k)) = fIdx from by omega]
        rw [hstart, insertAt_eraseIdx emptyHash (stack.drop (stack.length - k))
            (fIdx - (stack.length - k)) (by rw [hdroplen]; omega)]
        have hmerged : naryMr (stack.drop (stack.length - k))
            = (mergeTopD k stack).getD (stack.length - k) emptyHash := by
          rw [List.getD_eq_getElem?_getD, mergeTopD, if_neg (by omega),
            List.getElem?_append_right (by rw [List.length_take]; omega),
            List.length_take, Nat.min_eq_left (by omega)]
          simp
        rw [hmerged]
        exact ih (mergeTopD k stack).length (by omega) (mergeTopD k stack)
          (stack.length - k) rfl (by omega)
      · rw [if_neg hge]
        have htk : fIdx < stack.length - k := by omega
        have htl : fIdx < (stack.take (stack.length - k)).length := by
          rw [List.length_take, Nat.min_eq_left (by omega)]; exact htk
        have hstart : stack.getD fIdx emptyHash = (mergeTopD k stack).getD fIdx emptyHash := by
          rw [mergeTopD, if_neg (by omega), List.getD_eq_getElem?_getD,
            List.getD_eq_getElem?_getD, List.getElem?_append_left htl,
            List.getElem?_take_of_lt htk]
        rw [hstart]
        exact ih (mergeTopD k stack).length (by omega) (mergeTopD k stack) fIdx rfl (by omega)

/-- `findFrontier` returns a slot at or beyond the starting counter. -/
private theorem findFrontier_slot_ge (k index : Nat) :
    ∀ (coords : List (Nat × Nat)) (c fIdx l h : Nat),
      findFrontier k index coords c = some (fIdx, l, h) → c ≤ fIdx := by
  intro coords
  induction coords with
  | nil => intro c fIdx l h hf; simp only [findFrontier, reduceCtorEq] at hf
  | cons p rest ih =>
    intro c fIdx l h hf
    obtain ⟨pl, ph⟩ := p
    rw [findFrontier] at hf
    split at hf
    · next hcond => simp only [Option.some.injEq, Prod.mk.injEq] at hf; omega
    · next hcond => have := ih (c + 1) fIdx l h hf; omega

/-- The slot `findFrontier` returns indexes the covering tile. -/
theorem findFrontier_spec (k index : Nat) :
    ∀ (coords : List (Nat × Nat)) (c fIdx l h : Nat),
      findFrontier k index coords c = some (fIdx, l, h) →
      coords[fIdx - c]? = some (l, h) ∧ l ≤ index ∧ index < l + k ^ h := by
  intro coords
  induction coords with
  | nil => intro c fIdx l h hf; simp only [findFrontier, reduceCtorEq] at hf
  | cons p rest ih =>
    intro c fIdx l h hf
    obtain ⟨pl, ph⟩ := p
    rw [findFrontier] at hf
    split at hf
    · next hcond =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨hfi, hl, hh⟩ := hf
        subst hl; subst hh
        refine ⟨?_, hcond.1, hcond.2⟩
        rw [show fIdx - c = 0 from by omega]
        rfl
    · next hcond =>
        obtain ⟨hget, hl, hh⟩ := ih (c + 1) fIdx l h hf
        have hge : c + 1 ≤ fIdx := findFrontier_slot_ge k index rest (c + 1) fIdx l h hf
        refine ⟨?_, hl, hh⟩
        rw [show fIdx - c = (fIdx - (c + 1)) + 1 from by omega, List.getElem?_cons_succ]
        exact hget

/-- **Completeness core: the honest path folds to the root.** The digit half
    folds the leaf up to its frontier-subtree root (`digitFold`); the grouping
    half folds that root through the frontier merges to the spine root
    (`honestGroupPath_folds`), with `kary_bridge` pinning the stack entries to
    the perfect roots. -/
theorem honest_path_folds (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (index : Nat) (hidx : index < cells.length) :
    foldNary (cells.getD index emptyHash)
      (honestInclusionPath k cells index) = karyRoot k cells := by
  set fr := frontierForSizeT k cells.length with hfr
  obtain ⟨fIdx, l, h, hff⟩ := findFrontier_cover k index fr 0 cells.length 0
    (by rw [hfr]; exact frontier_tiles k cells.length hk) (by omega) hidx
  have hcover := (findFrontier_spec k index fr 0 fIdx l h hff).2
  have hfe : fr[fIdx]? = some (l, h) := by
    have := (findFrontier_spec k index fr 0 fIdx l h hff).1; simpa using this
  have hbuild : buildStackCells k cells = fr.map (fun lh => perfectRoot k cells lh.1 lh.2) := by
    rw [hfr]; exact kary_bridge k hk cells
  have hfidxlt : fIdx < fr.length := by
    simpa using findFrontier_slot_lt k index fr 0 fIdx l h hff
  have hpath : honestInclusionPath k cells index =
      honestDigitPath k cells l (index - l) h ++
        honestGroupPath k (buildStackCells k cells) fIdx := by
    rw [honestInclusionPath, ← hfr, hff]
  rw [hpath, foldNary, List.foldl_append, ← foldNary, ← foldNary]
  have hleaf : cells.getD index emptyHash = cells.getD (l + (index - l)) emptyHash := by
    congr 1; omega
  rw [hleaf, digitFold k hk cells l h (index - l),
    show (index - l) / k ^ h = 0 from Nat.div_eq_of_lt (by omega), Nat.zero_mul, Nat.add_zero]
  have hentry : (buildStackCells k cells).getD fIdx emptyHash = perfectRoot k cells l h := by
    rw [hbuild, List.getD_eq_getElem?_getD, List.getElem?_map, hfe]; rfl
  rw [← hentry, karyRoot,
    honestGroupPath_folds k hk (buildStackCells k cells).length
      (buildStackCells k cells) fIdx rfl (by rw [hbuild, List.length_map]; exact hfidxlt)]

/-- **Completeness: honest proofs verify** — previously claimed nowhere.
    Also the non-vacuity witness: `AcceptsKary` is satisfiable for every
    in-range `(index, cells)`, so the soundness theorem below quantifies
    over a provably non-empty accept set.
    *Strategy:* assemble `honest_path_shape` + `honest_path_folds`. -/
theorem kary_completeness (k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (index : Nat) (hidx : index < cells.length) :
    AcceptsKary k (cells.getD index emptyHash) index cells.length
      (karyRoot k cells) (honestInclusionPath k cells index) := by
  obtain ⟨⟨skel, hskel, hmap⟩, hwf⟩ := honest_path_shape k hk cells index hidx
  have hlen : skel.length = (honestInclusionPath k cells index).length := by
    rw [← hmap, List.length_map]
  refine ⟨hk, by omega, hidx, ⟨skel, hskel, by omega, ?_⟩, hwf,
    honest_path_folds k hk cells index hidx⟩
  rw [show (honestInclusionPath k cells index).length - skel.length = 0 from by omega,
    List.drop_zero, hmap]

/-- **Verifier soundness (existential in depth): accept ⇒ committed at
    `index`.** If the verifier accepts `(leaf, index, path)` against the
    honest root over `cells`, then the trailing skeleton steps bind the
    digest reached after the `d`-step prefix to *the level-0 cell at log
    position `index`* — i.e. `leaf` is committed at position `index`, at
    some depth `d` within that position's cell (depth is existential by
    design: implicit promotion makes depth unbindable, Cyphr SPEC §2.2.12;
    in flat logs honest `d = 0` and the cell is the leaf hash, in subtree
    logs the cell is the subtree root and the prefix is the within-subtree
    path).

    This is the V9 security-critical statement: the previous corpus-level
    `inclusion_soundness` delegated all content to an abstract
    `SkeletonValid`; here the skeleton is the concrete `inclusionSkeleton`
    and the fold is the real null-promoting one.

    *Strategy (completeness + uniqueness — no new induction):* split `path`
    at `d := path.length - skel.length`. The suffix shape-matches `skel`
    (from `StructureOK`); the honest path shape-matches `skel` with no
    prefix (`honest_path_shape`). Both fold to `root` — the suffix from
    `foldNary leaf (take d)` (fold-append decomposition,
    `List.foldl_append`), the honest path from the cell
    (`honest_path_folds`). Apply `foldNary_unique_of_shape` to the pair;
    its starting-digest conclusion is exactly the binding. -/
theorem kary_inclusion_soundness (k : Nat) (cells : List Digest)
    (leaf root : Digest) (index : Nat) (path : List ProofStep)
    (hacc : AcceptsKary k leaf index cells.length root path)
    (hroot : root = karyRoot k cells)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    ∃ (d : Nat) (skel : List (Nat × Nat)),
      inclusionSkeleton k cells.length index = some skel ∧
      d + skel.length = path.length ∧
      foldNary leaf (path.take d) = cells.getD index emptyHash := by
  obtain ⟨hk, _htree, hidx, ⟨skel, hskel, hsklen, hsuffix⟩, hwf, hfold⟩ := hacc
  obtain ⟨⟨skel', hskel', hhmap⟩, hhwf⟩ := honest_path_shape k hk cells index hidx
  have hhfold := honest_path_folds k hk cells index hidx
  have hskeleq : skel' = skel := Option.some_injective _ (hskel'.symm.trans hskel)
  refine ⟨path.length - skel.length, skel, hskel, by omega, ?_⟩
  set d := path.length - skel.length with hd
  have hshape : (path.drop d).map stepShape =
      (honestInclusionPath k cells index).map stepShape := by
    rw [hsuffix, hhmap, hskeleq]
  have hwfdrop : WellFormedSteps (path.drop d) :=
    fun s hs => hwf s (List.mem_of_mem_drop hs)
  have hcompose : foldNary (foldNary leaf (path.take d)) (path.drop d)
      = foldNary leaf path := by
    conv_rhs => rw [← List.take_append_drop d path]
    simp only [foldNary, List.foldl_append]
  have hfeq : foldNary (foldNary leaf (path.take d)) (path.drop d)
      = foldNary (cells.getD index emptyHash) (honestInclusionPath k cells index) := by
    rw [hcompose, hfold, hroot, hhfold]
  obtain ⟨hab, _⟩ := foldNary_unique_of_shape (foldNary leaf (path.take d))
    (cells.getD index emptyHash) (path.drop d) (honestInclusionPath k cells index)
    hshape hwfdrop hhwf hfeq hH hN
  exact hab

/-! ## `karyRoot` injectivity — the bag canonical-uniqueness theorem

The unprefixed `nary_mr` fold over the frontier peaks (`karyRoot` =
`foldFrontierRoot` over the per-coordinate `perfectRoot`s) is **injective over
equal-length cell lists**. This is the formal discharge of the MMR "no size
prefix" decision (`cml/src/mountain.rs`): the peak bag deliberately omits the
`H(size ‖ peak ‖ acc)` size prefix that OpenTimestamps/Grin use to guard
cross-size confusion, because `tree_size` is a trusted verifier parameter and the
anti-confusion job is done by *proven uniqueness* (this theorem) plus the trusted
size — not a prefix.

Lifted here from the consistency layer to its natural home: it is pure structural
injectivity about `karyRoot`/`perfectRoot`/`foldFrontierRoot`/`naryMr` (all
defined above), with no consistency-proof dependency, so both the consistency
layer and the durability/mountain layer consume it from the spine. -/

/-- Every index in `[start, stop)` lands in some tile of a `Tiles`
    decomposition. -/
private theorem Tiles_covers (k : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop : Nat), Tiles k start coords stop →
      ∀ i, start ≤ i → i < stop → ∃ c ∈ coords, c.1 ≤ i ∧ i < c.1 + k ^ c.2 := by
  intro coords
  induction coords with
  | nil => intro start stop htiles i hs hi; simp only [Tiles] at htiles; omega
  | cons p rest ih =>
    intro start stop htiles i hs hi
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    by_cases hlt : i < start + k ^ ph
    · refine ⟨(pl, ph), ?_, ?_, ?_⟩
      · simp
      · show pl ≤ i; omega
      · show i < pl + k ^ ph; omega
    · obtain ⟨c, hc, h1, h2⟩ := ih (start + k ^ ph) stop htrest i (by omega) hi
      exact ⟨c, List.mem_cons_of_mem _ hc, h1, h2⟩

/-- **`perfectRoot` injectivity over a span.** Equal perfect-subtree roots over
    `xs` and `ys` force the two cell lists to agree at every index the subtree
    covers — or a hash assumption broke. Induction on height, `naryMr_inj_of_length`
    at each level. -/
private theorem perfectRoot_inj (k : Nat) (hk : 2 ≤ k)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) (xs ys : List Digest) :
    ∀ (h left : Nat), perfectRoot k xs left h = perfectRoot k ys left h →
      ∀ i, i < k ^ h → xs.getD (left + i) emptyHash = ys.getD (left + i) emptyHash := by
  intro h
  induction h with
  | zero =>
    intro left heq i hi
    simp only [pow_zero, Nat.lt_one_iff] at hi
    subst hi
    simpa only [perfectRoot, Nat.add_zero] using heq
  | succ n ih =>
    intro left heq i hi
    have eL : perfectRoot k xs left (n + 1)
        = naryMr ((List.range k).map (fun j => perfectRoot k xs (left + j * k ^ n) n)) := by
      rw [perfectRoot]
    have eR : perfectRoot k ys left (n + 1)
        = naryMr ((List.range k).map (fun j => perfectRoot k ys (left + j * k ^ n) n)) := by
      rw [perfectRoot]
    rw [eL, eR] at heq
    have h2 : 2 ≤ ((List.range k).map
        (fun j => perfectRoot k xs (left + j * k ^ n) n)).length := by simp; omega
    have hlen : ((List.range k).map (fun j => perfectRoot k xs (left + j * k ^ n) n)).length
        = ((List.range k).map (fun j => perfectRoot k ys (left + j * k ^ n) n)).length := by simp
    have hmapeq := naryMr_inj_of_length _ _ hlen h2 heq hH hN
    -- per-child equality
    have hchild : ∀ j, j < k →
        perfectRoot k xs (left + j * k ^ n) n = perfectRoot k ys (left + j * k ^ n) n :=
      fun j hj => List.map_inj_left.mp hmapeq j (List.mem_range.mpr hj)
    -- decompose i = j*k^n + r
    have hkn : 0 < k ^ n := pow_pos (by omega) n
    have hj : i / k ^ n < k := by
      have hpow : k ^ (n + 1) = k ^ n * k := pow_succ k n
      rw [hpow] at hi
      exact Nat.div_lt_of_lt_mul hi
    have hr : i % k ^ n < k ^ n := Nat.mod_lt _ hkn
    have hdecomp : left + i = (left + (i / k ^ n) * k ^ n) + i % k ^ n := by
      have hdm := Nat.div_add_mod i (k ^ n)
      have hc : (i / k ^ n) * k ^ n = k ^ n * (i / k ^ n) := Nat.mul_comm _ _
      omega
    rw [hdecomp]
    exact ih (left + (i / k ^ n) * k ^ n) (hchild _ hj) (i % k ^ n) hr

/-- `naryMr` injectivity extended to **all** equal lengths (including the
    empty and singleton cases the length-≥2 version excludes): the empty/empty
    and singleton/singleton arms are promotion (no hashing). -/
private theorem naryMr_inj_eqlen (xs ys : List Digest)
    (hlen : xs.length = ys.length) (heq : naryMr xs = naryMr ys)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) : xs = ys := by
  rcases xs with _ | ⟨a, xs'⟩
  · rcases ys with _ | ⟨c, ys'⟩
    · rfl
    · simp only [List.length_nil, List.length_cons] at hlen; omega
  · rcases ys with _ | ⟨c, ys'⟩
    · simp only [List.length_nil, List.length_cons] at hlen; omega
    · rcases xs' with _ | ⟨b, s⟩
      · rcases ys' with _ | ⟨d, t⟩
        · have e1 : naryMr [a] = a := rfl
          have e2 : naryMr [c] = c := rfl
          rw [e1, e2] at heq; rw [heq]
        · simp only [List.length_cons, List.length_nil] at hlen; omega
      · rcases ys' with _ | ⟨d, t⟩
        · simp only [List.length_cons, List.length_nil] at hlen; omega
        · exact naryMr_inj_of_length _ _ hlen (by simp) heq hH hN

/-- **`foldFrontierRoot` injectivity over equal-length stacks.** Two stacks of
    equal length folding to the same spine root coincide — or a hash assumption
    broke. Strong induction on the (shared) length: the merge schedule is
    length-determined, so each `mergeTopD` step stays aligned and inverts via
    `naryMr_inj_of_length`. -/
private theorem foldFrontierRoot_inj (k : Nat) (hk : 2 ≤ k)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    ∀ (n : Nat) (xs ys : List Digest), xs.length = n → ys.length = n →
      foldFrontierRoot k xs = foldFrontierRoot k ys → xs = ys := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro xs ys hx hy heq
    by_cases hbase : xs.length ≤ k
    · have hbx : k < 2 ∨ xs.length ≤ k := Or.inr hbase
      have hby : k < 2 ∨ ys.length ≤ k := Or.inr (by omega)
      rw [foldFrontierRoot, dif_pos hbx] at heq
      conv_rhs at heq => rw [foldFrontierRoot, dif_pos hby]
      -- heq : naryMr xs = naryMr ys
      exact naryMr_inj_eqlen xs ys (by omega) heq hH hN
    · push_neg at hbase
      have hbx : ¬(k < 2 ∨ xs.length ≤ k) := by push_neg; exact ⟨by omega, by omega⟩
      have hby : ¬(k < 2 ∨ ys.length ≤ k) := by push_neg; exact ⟨by omega, by omega⟩
      rw [foldFrontierRoot, dif_neg hbx] at heq
      conv_rhs at heq => rw [foldFrontierRoot, dif_neg hby]
      have hmx : (mergeTopD k xs).length = n - k + 1 := by
        rw [mergeTopD, if_neg (by omega)]; simp only [List.length_append, List.length_take,
          List.length_cons, List.length_nil]; omega
      have hmy : (mergeTopD k ys).length = n - k + 1 := by
        rw [mergeTopD, if_neg (by omega)]; simp only [List.length_append, List.length_take,
          List.length_cons, List.length_nil]; omega
      have hmerge := ih (n - k + 1) (by omega) (mergeTopD k xs) (mergeTopD k ys) hmx hmy heq
      -- mergeTopD xs = mergeTopD ys  ⇒  xs = ys
      rw [mergeTopD, if_neg (by omega), mergeTopD, if_neg (by omega)] at hmerge
      have hlenx : (xs.take (xs.length - k)).length = (ys.take (ys.length - k)).length := by
        simp only [List.length_take]; omega
      obtain ⟨htake, hsnoc⟩ := List.append_inj hmerge hlenx
      have hdrop2 : 2 ≤ (xs.drop (xs.length - k)).length := by
        simp only [List.length_drop]; omega
      have hdroplen : (xs.drop (xs.length - k)).length = (ys.drop (ys.length - k)).length := by
        simp only [List.length_drop]; omega
      have hnary : naryMr (xs.drop (xs.length - k)) = naryMr (ys.drop (ys.length - k)) := by
        have := List.cons.inj hsnoc; exact this.1
      have hdrop := naryMr_inj_of_length _ _ hdroplen hdrop2 hnary hH hN
      calc xs = xs.take (xs.length - k) ++ xs.drop (xs.length - k) := (List.take_append_drop _ _).symm
        _ = ys.take (ys.length - k) ++ ys.drop (ys.length - k) := by rw [htake, hdrop]
        _ = ys := List.take_append_drop _ _

/-- **Bag canonical-uniqueness: `karyRoot` injectivity over equal-length cell
    lists.** Two cell lists of the same length with equal k-ary root coincide —
    or a hash assumption broke. Equal length is essential: by the
    flat-null-promotion design, all-null lists of *different* lengths share a root
    (`naryRoot = nullDigest`), so injectivity can only hold once length is pinned
    (which the trusted `tree_size` does). The k-ary analog of
    `naryMr_inj_of_length` lifted from one node to the whole unprefixed peak fold.

    *Strategy:* induct on the frontier structure / `foldFrontierRoot`, applying
    `naryMr_inj_of_length` at each merge; the equal-length hypothesis keeps the
    two folds shape-aligned. -/
theorem karyRoot_inj_of_length (k : Nat) (hk : 2 ≤ k) (xs ys : List Digest)
    (hlen : xs.length = ys.length) (heq : karyRoot k xs = karyRoot k ys)
    (hH : ¬NodeHashCollision) (hN : ¬CollapseAmbiguity) :
    xs = ys := by
  rw [karyRoot, karyRoot, kary_bridge k hk xs, kary_bridge k hk ys, ← hlen] at heq
  set F := frontierForSizeT k xs.length with hF
  have hstacklen : (F.map (fun lh => perfectRoot k xs lh.1 lh.2)).length
      = (F.map (fun lh => perfectRoot k ys lh.1 lh.2)).length := by simp
  have hmaps := foldFrontierRoot_inj k hk hH hN _ _ _ rfl hstacklen.symm heq
  -- per-coordinate root equality
  have hcoord : ∀ c ∈ F, perfectRoot k xs c.1 c.2 = perfectRoot k ys c.1 c.2 :=
    fun c hc => List.map_inj_left.mp hmaps c hc
  -- index-wise equality via tiling
  have hcover := Tiles_covers k F 0 xs.length (frontier_tiles k xs.length hk)
  have hpt : ∀ i, i < xs.length → xs.getD i emptyHash = ys.getD i emptyHash := by
    intro i hi
    obtain ⟨c, hc, h1, h2⟩ := hcover i (by omega) hi
    have hpr := perfectRoot_inj k hk hH hN xs ys c.2 c.1 (hcoord c hc) (i - c.1) (by omega)
    rwa [show c.1 + (i - c.1) = i from by omega] at hpr
  apply List.ext_getElem hlen
  intro i h1 h2
  have hp := hpt i h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at hp
  exact hp

/-! ## Frontier block-height monotonicity

The greedy k-ary decomposition only ever merges a fixed leaf's perfect subtree
**upward** as the log grows: the height of the mountain containing `index` is
monotone non-decreasing in the tree size. This is the structural invariant behind
durable witnesses (`EMLProof.Durability`) and the consistency layer's
`new_height ≥ boundary_height` guard — proven here once, generally, via the
base-`k` digit recursion `frontier_divstep`. -/

/-- `Covers k index n h`: leaf `index` sits in a height-`h` mountain of the
    size-`n` frontier. The membership-and-span relation `findFrontier`/the
    inclusion skeleton pin a proof against. -/
def Covers (k index n h : Nat) : Prop :=
  ∃ l, (l, h) ∈ frontierForSizeT k n ∧ l ≤ index ∧ index < l + k ^ h

/-- A scaled mountain is in the larger frontier: `(l, h) ∈ frontier a` lifts to
    `(l·k, h+1) ∈ frontier (a·k + b)` for `b < k` (the `frontier_divstep`
    scaled prefix). -/
private theorem mem_scaled_of_mem (k : Nat) (hk : 2 ≤ k) (a b l h : Nat) (hb : b < k)
    (hmem : (l, h) ∈ frontierForSizeT k a) :
    (l * k, h + 1) ∈ frontierForSizeT k (a * k + b) := by
  rw [frontier_divstep k hk a b hb]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨(l, h), hmem, rfl⟩)

/-- **Covers lifts under base-`k` scaling.** If `index / k`'s mountain at size
    `a` has height `h₀`, then `index`'s mountain at size `a·k + b` (`b < k`) has
    height `h₀ + 1` — the scaled-prefix half of the digit recursion. -/
private theorem covers_scale (k : Nat) (hk : 2 ≤ k) (a b index h₀ : Nat) (hb : b < k)
    (hinner : Covers k (index / k) a h₀) : Covers k index (a * k + b) (h₀ + 1) := by
  obtain ⟨l, hmem, hsl, hslt⟩ := hinner
  refine ⟨l * k, mem_scaled_of_mem k hk a b l h₀ hb hmem, ?_, ?_⟩
  · -- l ≤ index/k ⟹ l*k ≤ index
    calc l * k ≤ index / k * k := Nat.mul_le_mul_right k hsl
      _ ≤ index := Nat.div_mul_le_self index k
  · -- index < l*k + k^(h₀+1) = (l + k^h₀)*k
    have hk0 : 0 < k := by omega
    have hub : index / k < l + k ^ h₀ := hslt
    have hdm : index / k * k + index % k = index := by
      have h := Nat.div_add_mod index k; rw [Nat.mul_comm] at h; omega
    have hmodlt : index % k < k := Nat.mod_lt index hk0
    have hstep : index < (index / k + 1) * k := by
      have : (index / k + 1) * k = index / k * k + k := by ring
      rw [this]; omega
    have hle : (index / k + 1) * k ≤ (l + k ^ h₀) * k := Nat.mul_le_mul_right k (by omega)
    have : index < (l + k ^ h₀) * k := Nat.lt_of_lt_of_le hstep hle
    calc index < (l + k ^ h₀) * k := this
      _ = l * k + k ^ (h₀ + 1) := by rw [Nat.add_mul, pow_succ]

/-- Every tile's left coordinate is at least the decomposition's start. -/
private theorem Tiles_left_ge' (k : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop : Nat), Tiles k start coords stop →
      ∀ lh ∈ coords, start ≤ lh.1 := by
  intro coords
  induction coords with
  | nil => intro start stop _ lh hmem; simp only [List.not_mem_nil] at hmem
  | cons p rest ih =>
    intro start stop htiles lh hmem
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem'
    · exact le_of_eq hpl.symm
    · have := ih (start + k ^ ph) stop htrest lh hmem'; omega

/-- **Tiles are disjoint.** In a `Tiles` decomposition, two member spans both
    containing `index` coincide — consecutive disjoint spans cannot both cover a
    point. Hence a leaf's mountain (height included) is unique per size. -/
private theorem Tiles_cover_unique (k index₀ : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop : Nat), Tiles k start coords stop →
      ∀ la ha lb hb, (la, ha) ∈ coords → la ≤ index₀ → index₀ < la + k ^ ha →
        (lb, hb) ∈ coords → lb ≤ index₀ → index₀ < lb + k ^ hb →
        (la, ha) = (lb, hb) := by
  intro coords
  induction coords with
  | nil => intro start stop _ la ha lb hb hma; simp only [List.not_mem_nil] at hma
  | cons p rest ih =>
    intro start stop htiles la ha lb hb hma hsla hslta hmb hslb hsltb
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    -- hpl : pl = start
    have hbound : ∀ l h, (l, h) ∈ rest → pl + k ^ ph ≤ l := by
      intro l h hm
      rw [hpl]
      exact Tiles_left_ge' k rest (start + k ^ ph) stop htrest (l, h) hm
    rw [List.mem_cons] at hma hmb
    rcases hma with hpa | hra <;> rcases hmb with hpb | hrb
    · rw [hpa, hpb]
    · exfalso
      injection hpa with hla hha; subst hla; subst hha
      have := hbound lb hb hrb; omega
    · exfalso
      injection hpb with hlb hhb; subst hlb; subst hhb
      have := hbound la ha hra; omega
    · exact ih (start + k ^ ph) stop htrest la ha lb hb hra hsla hslta hrb hslb hsltb

/-- **Frontier block-height monotonicity.** For a fixed `index`, growing the tree
    never lowers the height of its containing mountain: `Covers k index n h` and
    `n ≤ n'` (`index < n`) give a mountain at `n'` of height `≥ h`. Proven by
    strong induction on `n` via the base-`k` digit recursion: `index` either falls
    in the scaled prefix (descend to `index / k` at `n / k ≤ n' / k`, +1 both
    sides) or is a fresh height-0 leaf (trivially `≤` anything). -/
theorem covers_mono (k : Nat) (hk : 2 ≤ k) :
    ∀ n index h n', Covers k index n h → index < n → n ≤ n' →
      ∃ h', Covers k index n' h' ∧ h ≤ h' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro index h n' hcov hidx hnn'
    have hk0 : 0 < k := by omega
    -- the size-n' mountain of index exists (index < n ≤ n', frontier tiles [0,n'))
    obtain ⟨fIdx', l', h', hff'⟩ := findFrontier_cover k index (frontierForSizeT k n') 0 n' 0
      (frontier_tiles k n' hk) (Nat.zero_le _) (by omega)
    obtain ⟨hget', hsl', hslt'⟩ := findFrontier_spec k index (frontierForSizeT k n') 0 fIdx' l' h' hff'
    have hmem' : (l', h') ∈ frontierForSizeT k n' := List.mem_of_getElem? (by simpa using hget')
    have hcov' : Covers k index n' h' := ⟨l', hmem', hsl', hslt'⟩
    -- it suffices to show h ≤ h'
    refine ⟨h', hcov', ?_⟩
    -- decompose by whether h = 0 (then trivial) else descend
    rcases Nat.eq_zero_or_pos h with hh0 | hhpos
    · omega
    -- h ≥ 1: index's mountain at n is scaled, so index < (n/k)*k and the inner
    -- mountain of index/k at n/k has height h-1. Recurse.
    obtain ⟨l, hmem, hsl, hslt⟩ := hcov
    -- n = (n/k)*k + n%k
    set a := n / k with ha
    set b := n % k with hb
    have hnab : n = a * k + b := by
      rw [ha, hb]; have h := Nat.div_add_mod n k; rw [Nat.mul_comm] at h; omega
    have hblt : b < k := Nat.mod_lt n hk0
    -- the size-n frontier splits; index's height-h (≥1) mountain must be in the scaled part
    have hsplit := frontier_divstep k hk a b hblt
    rw [← hnab] at hsplit
    rw [hsplit, List.mem_append] at hmem
    rcases hmem with hsc | hleaf
    · -- scaled: (l,h) = (l₀*k, h₀+1) with (l₀,h₀) ∈ frontier a
      rw [List.mem_map] at hsc
      obtain ⟨⟨l₀, h₀⟩, hmem₀, heq⟩ := hsc
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hl, hh⟩ := heq
      -- h = h₀ + 1, l = l₀ * k
      -- l₀ + k^h₀ ≤ a: the inner block fits in frontier a
      have hinnerfit : l₀ + k ^ h₀ ≤ a :=
        Tiles_entry_bound k (frontierForSizeT k a) 0 a (frontier_tiles k a hk) (l₀, h₀) hmem₀
      have hil₀ : l₀ ≤ index / k := by
        rw [← hl] at hsl; exact (Nat.le_div_iff_mul_le hk0).mpr hsl
      have hiu₀ : index / k < l₀ + k ^ h₀ := by
        rw [← hl, ← hh] at hslt
        have hexp : l₀ * k + k ^ (h₀ + 1) = k * (l₀ + k ^ h₀) := by rw [pow_succ]; ring
        rw [hexp] at hslt
        exact Nat.div_lt_of_lt_mul hslt
      have hcovInner : Covers k (index / k) a h₀ := ⟨l₀, hmem₀, hil₀, hiu₀⟩
      have haidx : index / k < a := lt_of_lt_of_le hiu₀ hinnerfit

      -- a ≤ n' / k? need n/k ≤ n'/k from n ≤ n'
      have han' : a ≤ n' / k := by rw [ha]; exact Nat.div_le_div_right hnn'
      -- recurse at a < n
      have haltn : a < n := by rw [ha]; exact Nat.div_lt_self (by omega) (by omega)
      obtain ⟨h₀', hcov₀', hle₀⟩ := ih a haltn (index / k) h₀ (n' / k) hcovInner haidx han'
      -- lift back: Covers k index n' (h₀'+1) and h = h₀+1 ≤ h₀'+1 ≤ h'
      have hcovLift : Covers k index ((n' / k) * k + n' % k) (h₀' + 1) :=
        covers_scale k hk (n' / k) (n' % k) index h₀' (Nat.mod_lt n' hk0) hcov₀'
      have hn'eq : (n' / k) * k + n' % k = n' := by
        have h := Nat.div_add_mod n' k; rw [Nat.mul_comm] at h; omega
      rw [hn'eq] at hcovLift
      -- two coverings of index at n' ⟹ same height (tiles disjoint) — or just compare
      -- h = h₀+1 ≤ h₀'+1; and the n'-covering height is unique, so h' ≥ h via hcovLift
      -- the size-n' mountain height of index is unique (tiles disjoint)
      obtain ⟨la, hma, hsla, hslta⟩ := hcov'
      obtain ⟨lb, hmb, hslb, hsltb⟩ := hcovLift
      have huniq := Tiles_cover_unique k index (frontierForSizeT k n') 0 n'
        (frontier_tiles k n' hk) la h' lb (h₀' + 1) hma hsla hslta hmb hslb hsltb
      injection huniq with _ hheq
      omega
    · -- leaf: (l,h) is a height-0 leaf, so h = 0, contradicting hhpos
      rw [List.mem_map] at hleaf
      obtain ⟨i, _, heq⟩ := hleaf
      simp only [Prod.mk.injEq] at heq
      omega

/-- **A leaf's mountain height is unique per size.** Two `Covers` witnesses for
    the same `index` and size `n` have equal height — the frontier tiles are
    disjoint. Lets a caller pin the height `covers_mono` produces to the one a
    concrete `findFrontier`/membership fact names. -/
theorem covers_height_unique (k index n h₁ h₂ : Nat) (hk : 2 ≤ k)
    (hc₁ : Covers k index n h₁) (hc₂ : Covers k index n h₂) : h₁ = h₂ := by
  obtain ⟨l₁, hm₁, hsl₁, hslt₁⟩ := hc₁
  obtain ⟨l₂, hm₂, hsl₂, hslt₂⟩ := hc₂
  have heq := Tiles_cover_unique k index (frontierForSizeT k n) 0 n (frontier_tiles k n hk)
    l₁ h₁ l₂ h₂ hm₁ hsl₁ hslt₁ hm₂ hsl₂ hslt₂
  exact congrArg Prod.snd heq

/-- **Frontier block height is monotone in size** (the `Covers`-level statement
    specialized to named heights). For a fixed `index < n ≤ n'`, the mountain
    height at `n` is `≤` the mountain height at `n'`. Durability's unconditional
    growth premise. -/
theorem frontier_height_mono (k index n h n' h' : Nat) (hk : 2 ≤ k)
    (hcn : Covers k index n h) (hidx : index < n) (hnn' : n ≤ n')
    (hcn' : Covers k index n' h') : h ≤ h' := by
  obtain ⟨h'', hc'', hle⟩ := covers_mono k hk n index h n' hcn hidx hnn'
  have : h'' = h' := covers_height_unique k index n' h'' h' hk hc'' hcn'
  omega

end NEML
