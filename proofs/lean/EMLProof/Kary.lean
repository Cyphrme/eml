import EMLProof.NEML
import Mathlib.Data.Nat.Log

/-!
# K-ary log-spine topology and verifier soundness (V9)

This module closes the V9 gap: the k-ary construction, the base-k carry
schedule, and the inclusion verifier were previously unmodeled — "formally
proven" covered only the honest binary construction, not the adversarial
input path.

Three layers, mirroring the shipped Rust:

1. **Topology** (`frontierForSizeT`, `reductionCount`, `inclusionSkeleton`):
   total transcriptions of `neml/src/topology.rs`. The legacy `partial def`
   models earlier in the corpus (`frontierForSize`, `buildTree`,
   `reconstructIndexFromPath` in `NEML.lean`) are opaque to the kernel and
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
   (`neml/src/proof.rs`): the trailing steps are pinned field-by-field
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
* `NullAmbiguity L` — some node of ≥ 2 *not-all-null* children hashes to
  exactly the null constant. With untagged `nodeHash = H(concat)` this is
  `H(child bytes) = H("null")`, i.e. an `H` collision unless the child
  bytes literally concatenate to the 4-byte string `"null"` (impossible for
  real digest widths, but `digestToBytes` is an axiom with no length
  constraint, so it is surfaced honestly as its own assumption).

## Status

⚠ The definitions below are total and compile; theorems marked `sorry` are
formulated and decomposed but not yet ground out. The README's sorry-free
claim applies to the pre-existing corpus, not yet to this module. Each
`sorry` carries a proof-strategy note.
-/

set_option linter.style.emptyLine false
set_option linter.unusedVariables false

namespace NEML

/-! ## Layer 1 — topology (total transcription of `neml/src/topology.rs`) -/

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
    in `n + 1`. Mirrors `topology… reduction_count` (`neml/src/lib.rs`):
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
private theorem findFrontier_slot_lt (k index : Nat) :
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
    silently in a proof. -/
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
/-- Null-promoting n-ary Merkle root, faithful to `mr.rs::nary_mr`:
    empty → `emptyHash`; singleton → promoted unchanged; otherwise null if
    *all* children are null, else `nodeHash`. The verifier's fold and the
    builder's merge both use this — never plain `nodeHash`. -/
noncomputable def naryMr (L : Nat) (children : List Digest) : Digest :=
  match children with
  | [] => emptyHash
  | [c] => c
  | cs => if ∀ c ∈ cs, c = nullDigest L then nullDigest L else nodeHash cs

/-- One digest-level merge of the top (rightmost) `k` stack entries. -/
noncomputable def mergeTopD (L k : Nat) (stack : List Digest) : List Digest :=
  if stack.length < k then stack
  else stack.take (stack.length - k) ++ [naryMr L (stack.drop (stack.length - k))]

theorem mergeTopD_length_lt (L k : Nat) (stack : List Digest)
    (hk : 2 ≤ k) (hlen : k < stack.length) :
    (mergeTopD L k stack).length < stack.length := by
  unfold mergeTopD
  rw [if_neg (by omega)]
  simp [List.length_take]
  omega

/-- Iterated digest-level merge. -/
noncomputable def mergeTopDN (L k : Nat) : Nat → List Digest → List Digest
  | 0, s => s
  | c + 1, s => mergeTopDN L k c (mergeTopD L k s)

/-- One append at index `idx`: push the cell, run the carry schedule.
    Faithful to the merge loop of `append_leaf`/`append_subtree`
    (`neml/src/tree.rs`), which merges via `nary_mr`. -/
noncomputable def appendCell (L k : Nat) (stack : List Digest) (cell : Digest)
    (idx : Nat) : List Digest :=
  mergeTopDN L k (reductionCount k idx) (stack ++ [cell])

noncomputable def buildStackGo (L k : Nat) (stack : List Digest) (idx : Nat) :
    List Digest → List Digest
  | [] => stack
  | c :: cs => buildStackGo L k (appendCell L k stack c idx) (idx + 1) cs

/-- The frontier stack after appending all level-0 `cells` in order. -/
noncomputable def buildStackCells (L k : Nat) (cells : List Digest) : List Digest :=
  buildStackGo L k [] 0 cells

/-- Canonical root of the perfect k-ary subtree of height `h` over
    `cells[left, left + k^h)`: children leftmost-first, folded with the
    same null-promoting `naryMr` the builder uses. Out-of-range cells
    default to `emptyHash` (irrelevant under the tiling hypothesis). -/
noncomputable def perfectRoot (L k : Nat) (cells : List Digest) (left : Nat) :
    Nat → Digest
  | 0 => cells.getD left emptyHash
  | h + 1 =>
      naryMr L ((List.range k).map fun j =>
        perfectRoot L k cells (left + j * k ^ h) h)

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
private theorem Tiles_entry_bound (k : Nat) :
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
private theorem buildStackGo_snoc (L k : Nat) :
    ∀ (cs : List Digest) (stack : List Digest) (idx : Nat) (c : Digest),
      buildStackGo L k stack idx (cs ++ [c]) =
        appendCell L k (buildStackGo L k stack idx cs) c (idx + cs.length) := by
  intro cs
  induction cs with
  | nil => intro stack idx c; simp [buildStackGo]
  | cons d ds ih =>
    intro stack idx c
    simp only [List.cons_append, buildStackGo]
    rw [ih (appendCell L k stack d idx) (idx + 1) c, List.length_cons,
      show idx + 1 + ds.length = idx + (ds.length + 1) by omega]

/-- `perfectRoot` only reads cells within the subtree span, so appending more
    cells beyond it leaves the root unchanged. -/
private theorem perfectRoot_stable (L k : Nat) (cells extra : List Digest) :
    ∀ (h left : Nat), left + k ^ h ≤ cells.length →
      perfectRoot L k cells left h = perfectRoot L k (cells ++ extra) left h := by
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
private theorem mergeTopD_sim (L k : Nat) (hk : 1 ≤ k) (cells : List Digest)
    (coords : List (Nat × Nat)) (hblock : IsBlockTop k coords) :
    mergeTopD L k (coords.map (fun lh => perfectRoot L k cells lh.1 lh.2)) =
      (mergeTopCoords k coords).map (fun lh => perfectRoot L k cells lh.1 lh.2) := by
  obtain ⟨hlen, l, h, hdrop⟩ := hblock
  have hnary : naryMr L ((coords.drop (coords.length - k)).map
      (fun lh => perfectRoot L k cells lh.1 lh.2)) = perfectRoot L k cells l (h + 1) := by
    rw [hdrop, List.map_map]
    conv_rhs => rw [perfectRoot]
    apply congrArg (naryMr L)
    apply List.map_congr_left
    intro i _
    simp [Function.comp]
  have hhead : (coords.drop (coords.length - k)).head? = some (l, h) := by
    rw [hdrop, List.head?_map]
    have hr : (List.range k).head? = some 0 := by
      rw [show k = (k - 1) + 1 by omega, List.range_succ_eq_map]; rfl
    rw [hr]; simp
  have hLHS : mergeTopD L k (coords.map (fun lh => perfectRoot L k cells lh.1 lh.2)) =
      (coords.take (coords.length - k)).map (fun lh => perfectRoot L k cells lh.1 lh.2) ++
        [perfectRoot L k cells l (h + 1)] := by
    unfold mergeTopD
    rw [List.length_map, if_neg (by omega), ← List.map_take, ← List.map_drop, hnary]
  have hRHS : (mergeTopCoords k coords).map (fun lh => perfectRoot L k cells lh.1 lh.2) =
      (coords.take (coords.length - k)).map (fun lh => perfectRoot L k cells lh.1 lh.2) ++
        [perfectRoot L k cells l (h + 1)] := by
    unfold mergeTopCoords
    rw [if_neg (by omega), hhead]
    simp
  rw [hLHS, hRHS]

/-- **Chained simulation.** If every intermediate state has a valid trailing
    block, the iterated digest merge tracks the iterated coordinate merge. -/
private theorem simChain (L k : Nat) (hk : 1 ≤ k) (cells : List Digest) :
    ∀ (c : Nat) (coords : List (Nat × Nat)),
      (∀ j < c, IsBlockTop k (mergeTopCoordsN k j coords)) →
      mergeTopDN L k c (coords.map (fun lh => perfectRoot L k cells lh.1 lh.2)) =
        (mergeTopCoordsN k c coords).map (fun lh => perfectRoot L k cells lh.1 lh.2) := by
  intro c
  induction c with
  | zero => intro coords _; rfl
  | succ c ih =>
    intro coords hvalid
    have hval' : ∀ j < c, IsBlockTop k (mergeTopCoordsN k j (mergeTopCoords k coords)) :=
      fun j hj => hvalid (j + 1) (by omega)
    show mergeTopDN L k c (mergeTopD L k (coords.map (fun lh => perfectRoot L k cells lh.1 lh.2)))
       = (mergeTopCoordsN k (c + 1) coords).map (fun lh => perfectRoot L k cells lh.1 lh.2)
    rw [mergeTopD_sim L k hk cells coords (hvalid 0 (by omega)),
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
theorem kary_bridge (L k : Nat) (hk : 2 ≤ k) (cells : List Digest) :
    buildStackCells L k cells =
      (frontierForSizeT k cells.length).map
        (fun lh => perfectRoot L k cells lh.1 lh.2) := by
  induction cells using List.reverseRecOn with
  | nil =>
    rw [buildStackCells, frontierForSizeT, frontierGo]
    simp [buildStackGo]
  | append_singleton cs c ih =>
    have hlenc : (cs ++ [c]).length = cs.length + 1 := by simp
    rw [buildStackCells, buildStackGo_snoc, Nat.zero_add,
      show buildStackGo L k [] 0 cs = buildStackCells L k cs from rfl, ih, appendCell]
    have hstab :
        (frontierForSizeT k cs.length).map (fun lh : Nat × Nat => perfectRoot L k cs lh.1 lh.2)
        = (frontierForSizeT k cs.length).map
            (fun lh : Nat × Nat => perfectRoot L k (cs ++ [c]) lh.1 lh.2) := by
      apply List.map_congr_left
      intro lh hlh
      exact perfectRoot_stable L k cs [c] lh.2 lh.1
        (Tiles_entry_bound k (frontierForSizeT k cs.length) 0 cs.length
          (frontier_tiles k cs.length hk) lh hlh)
    have hc : perfectRoot L k (cs ++ [c]) cs.length 0 = c := by
      show (cs ++ [c]).getD cs.length emptyHash = c
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        show cs.length - cs.length = 0 from by omega]
      rfl
    have hmerge :
        (frontierForSizeT k cs.length).map (fun lh : Nat × Nat => perfectRoot L k cs lh.1 lh.2) ++ [c]
        = (frontierForSizeT k cs.length ++ [(cs.length, 0)]).map
            (fun lh : Nat × Nat => perfectRoot L k (cs ++ [c]) lh.1 lh.2) := by
      rw [hstab, List.map_append, List.map_cons, List.map_nil, hc]
    rw [hmerge,
      simChain L k (by omega) (cs ++ [c]) (reductionCount k cs.length)
        (frontierForSizeT k cs.length ++ [(cs.length, 0)]) (validCarry k hk cs.length),
      ← frontier_append_consistent k cs.length hk, hlenc]

/-- Fold the frontier stack to the spine root: merge the rightmost `k` while
    more than `k` remain, then one final `naryMr` (which also covers the
    empty → `emptyHash` and singleton-promotion cases). Mirrors
    `compute_root_from_state` (`neml/src/tree.rs`) and the fold described in
    `topology.rs` module docs. -/
noncomputable def foldFrontierRoot (L k : Nat) (stack : List Digest) : Digest :=
  if h : k < 2 ∨ stack.length ≤ k then naryMr L stack
  else foldFrontierRoot L k (mergeTopD L k stack)
termination_by stack.length
decreasing_by
  push_neg at h
  exact mergeTopD_length_lt L k stack (by omega) h.2

/-- The per-algorithm raw root over level-0 `cells` (flat: leaf hashes;
    subtree kind: stored subtree roots). -/
noncomputable def karyRoot (L k : Nat) (cells : List Digest) : Digest :=
  foldFrontierRoot L k (buildStackCells L k cells)

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
noncomputable def applyStepN (L : Nat) (cur : Digest) (s : ProofStep) : Digest :=
  naryMr L (insertAt s.position cur s.siblings)

/-- The verifier's root reconstruction (`reconstruct_inclusion_root` fold). -/
noncomputable def foldNary (L : Nat) (leaf : Digest) (path : List ProofStep) : Digest :=
  path.foldl (applyStepN L) leaf

/-- The accept relation of `verify_inclusion`, minus DoS bounds:
    range guards, skeleton pinning, canonical well-formedness, and the
    fold reaching `root`. -/
def AcceptsKary (L k : Nat) (leaf : Digest) (index treeSize : Nat)
    (root : Digest) (path : List ProofStep) : Prop :=
  2 ≤ k ∧ 0 < treeSize ∧ index < treeSize ∧
  StructureOK k index treeSize path ∧
  WellFormedSteps path ∧
  foldNary L leaf path = root

/-- A node of ≥ 2 not-all-null children whose `nodeHash` is exactly the null
    constant. Untagged `nodeHash = H(concat of digest bytes)` makes this an
    `H` collision unless the child bytes concatenate to the literal 4-byte
    `"null"` preimage; `digestToBytes` is an unconstrained axiom, so the
    case is surfaced as an explicit assumption rather than argued away. -/
def NullAmbiguity (L : Nat) : Prop :=
  ∃ cs : List Digest, 2 ≤ cs.length ∧ ¬(∀ c ∈ cs, c = nullDigest L) ∧
    nodeHash cs = nullDigest L

/-- **Fixed-arity injectivity of `naryMr`.** Same-length child lists of
    length ≥ 2 with equal `naryMr` are equal — or a hash assumption broke.
    The null-promotion analysis: two all-null lists of equal length are
    *elementwise* equal (this is why same-length matters: all-null lists of
    different lengths collide under `naryMr` by design, which is exactly
    what the skeleton's arity pinning excludes); mixed null/non-null is
    `NullAmbiguity`; both non-null reduces to `NodeHashCollision`.
    *Strategy:* case on the two `if`s; the all-null/all-null case is
    `List.ext` via length + pointwise `nullDigest`. -/
theorem naryMr_inj_of_length (L : Nat) (xs ys : List Digest)
    (hlen : xs.length = ys.length) (h2 : 2 ≤ xs.length)
    (heq : naryMr L xs = naryMr L ys)
    (hH : ¬NodeHashCollision) (hN : ¬NullAmbiguity L) :
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
  by_cases hxn : ∀ z ∈ a :: b :: xr, z = nullDigest L
  · by_cases hyn : ∀ z ∈ c :: d :: yr, z = nullDigest L
    · -- Both all-null and same length ⇒ elementwise equal.
      apply List.ext_getElem hlen
      intro i h1 h2'
      rw [hxn _ (List.getElem_mem h1), hyn _ (List.getElem_mem h2')]
    · -- `xs` all-null, `ys` not ⇒ `nodeHash ys = nullDigest L`: NullAmbiguity.
      rw [if_pos hxn, if_neg hyn] at heq
      exact absurd ⟨c :: d :: yr, hys2, hyn, heq.symm⟩ hN
  · by_cases hyn : ∀ z ∈ c :: d :: yr, z = nullDigest L
    · rw [if_neg hxn, if_pos hyn] at heq
      exact absurd ⟨a :: b :: xr, h2, hxn, heq⟩ hN
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
private theorem foldNary_append_last (L : Nat) (a : Digest)
    (p' : List ProofStep) (s : ProofStep) :
    foldNary L a (p' ++ [s]) = applyStepN L (foldNary L a p') s := by
  simp only [foldNary, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem foldNary_unique_aux (L : Nat)
    (hH : ¬NodeHashCollision) (hN : ¬NullAmbiguity L) :
    ∀ (n : Nat) (a b : Digest) (p q : List ProofStep),
      p.length = n → q.length = n →
      p.map stepShape = q.map stepShape →
      WellFormedSteps p → WellFormedSteps q →
      foldNary L a p = foldNary L b q →
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
    have hxs2 : 2 ≤ (insertAt s₁.position (foldNary L a p') s₁.siblings).length := by
      rw [insertAt_length]
      have hne : s₁.siblings.length ≠ 0 := fun h0 =>
        hwf_s1.1 (List.eq_nil_of_length_eq_zero h0)
      omega
    have hxylen :
        (insertAt s₁.position (foldNary L a p') s₁.siblings).length =
          (insertAt s₂.position (foldNary L b q') s₂.siblings).length := by
      rw [insertAt_length, insertAt_length, hsiblen]
    have hnode := naryMr_inj_of_length L _ _ hxylen hxs2 heq hH hN
    rw [hpos] at hnode
    obtain ⟨hfold, hsib⟩ :=
      insertAt_injective s₂.position (foldNary L a p') (foldNary L b q')
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
    `foldCanonical_unique_of_len` (NEML.lean), whose induction structure
    (back-decomposition of both paths, `insertAt_injective` per step) is
    the template; each step applies `naryMr_inj_of_length`, with
    `insertAt` preserving the pinned length
    (`(insertAt p c s).length = s.length + 1 ≥ 2` from `WellFormedSteps`). -/
theorem foldNary_unique_of_shape (L : Nat) (a b : Digest)
    (p q : List ProofStep)
    (hshape : p.map stepShape = q.map stepShape)
    (hwfp : WellFormedSteps p) (hwfq : WellFormedSteps q)
    (heq : foldNary L a p = foldNary L b q)
    (hH : ¬NodeHashCollision) (hN : ¬NullAmbiguity L) :
    a = b ∧ p = q := by
  have hlenpq : p.length = q.length := by
    have := congrArg List.length hshape
    simpa using this
  exact foldNary_unique_aux L hH hN p.length a b p q rfl hlenpq.symm
    hshape hwfp hwfq heq

/-! ### The honest prover -/

/-- Honest within-subtree digit path for offset `offset` in the frontier
    subtree at `(left, h)`: at level `j` the path node sits at digit
    `(offset / k^j) % k` among the `k` children of the level-`j+1` block;
    siblings are the other `k - 1` perfect roots, in child order. -/
noncomputable def honestDigitPath (L k : Nat) (cells : List Digest)
    (left offset h : Nat) : List ProofStep :=
  (List.range h).map fun j =>
    { position := offset / k ^ j % k,
      siblings := ((List.range k).filter (fun i => i != offset / k ^ j % k)).map
        fun i => perfectRoot L k cells (left + (offset / k ^ (j + 1) * k + i) * k ^ j) j }

/-- Honest grouping path: replay the frontier fold, emitting a step (with
    the other merge participants as siblings, path node erased) whenever the
    tracked slot is inside the merged window. Same recursion as
    `groupingSteps`, carrying digests. -/
noncomputable def honestGroupPath (L k : Nat) (stack : List Digest)
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
        honestGroupPath L k (mergeTopD L k stack) (stack.length - k)
    else
      honestGroupPath L k (mergeTopD L k stack) fIdx
termination_by stack.length
decreasing_by
  all_goals (push_neg at h; exact mergeTopD_length_lt L k stack (by omega) h.2)

/-- The honest inclusion path for log position `index`: digit steps inside
    its frontier subtree, then grouping steps to the spine root. Mirrors
    proof generation (which derives the same skeleton from
    `inclusion_skeleton`). -/
noncomputable def honestInclusionPath (L k : Nat) (cells : List Digest)
    (index : Nat) : List ProofStep :=
  match findFrontier k index (frontierForSizeT k cells.length) 0 with
  | none => []
  | some (fIdx, l, h) =>
      honestDigitPath L k cells l (index - l) h ++
        honestGroupPath L k (buildStackCells L k cells) fIdx

/-- The honest path realizes the skeleton exactly (no prefix: `d = 0` at the
    cell level) and is well-formed.
    *Strategy:* digit half — `List.length_filter` count of `i != pos` over
    `range k` is `k - 1`, positions match `digitSteps` pointwise; grouping
    half — induction on the shared recursion of `honestGroupPath` /
    `groupingSteps` with `kary_bridge` fixing the stack length to the
    frontier length; `eraseIdx` length arithmetic gives sibling counts. -/
theorem honest_path_shape (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (index : Nat) (hidx : index < cells.length) :
    (∃ skel, inclusionSkeleton k cells.length index = some skel ∧
      (honestInclusionPath L k cells index).map stepShape = skel) ∧
    WellFormedSteps (honestInclusionPath L k cells index) := by
  sorry

/-- **Completeness core: the honest path folds to the root.**
    *Strategy:* digit half by induction on `h` — folding one digit step
    re-inserts the path node among its siblings, reassembling exactly the
    `List.range k` child list of `perfectRoot (j+1)` (`insertAt` of the
    erased element at its own position is the identity reassembly);
    grouping half by the `honestGroupPath` recursion against
    `foldFrontierRoot`, with `kary_bridge` supplying that the stack entries
    are the perfect roots and the tracked entry is the running fold. -/
theorem honest_path_folds (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (index : Nat) (hidx : index < cells.length) :
    foldNary L (cells.getD index emptyHash)
      (honestInclusionPath L k cells index) = karyRoot L k cells := by
  sorry

/-- **Completeness: honest proofs verify** — previously claimed nowhere.
    Also the non-vacuity witness: `AcceptsKary` is satisfiable for every
    in-range `(index, cells)`, so the soundness theorem below quantifies
    over a provably non-empty accept set.
    *Strategy:* assemble `honest_path_shape` + `honest_path_folds`. -/
theorem kary_completeness (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (index : Nat) (hidx : index < cells.length) :
    AcceptsKary L k (cells.getD index emptyHash) index cells.length
      (karyRoot L k cells) (honestInclusionPath L k cells index) := by
  sorry

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
    `foldNary L leaf (take d)` (fold-append decomposition,
    `List.foldl_append`), the honest path from the cell
    (`honest_path_folds`). Apply `foldNary_unique_of_shape` to the pair;
    its starting-digest conclusion is exactly the binding. -/
theorem kary_inclusion_soundness (L k : Nat) (cells : List Digest)
    (leaf root : Digest) (index : Nat) (path : List ProofStep)
    (hacc : AcceptsKary L k leaf index cells.length root path)
    (hroot : root = karyRoot L k cells)
    (hH : ¬NodeHashCollision) (hN : ¬NullAmbiguity L) :
    ∃ (d : Nat) (skel : List (Nat × Nat)),
      inclusionSkeleton k cells.length index = some skel ∧
      d + skel.length = path.length ∧
      foldNary L leaf (path.take d) = cells.getD index emptyHash := by
  sorry

end NEML
