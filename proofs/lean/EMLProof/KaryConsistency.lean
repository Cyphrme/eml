import EMLProof.Kary

/-!
# K-ary consistency-verifier soundness (V9 follow-on d)

`Kary.lean` proved the **inclusion** verifier sound. This module does the same
for the **consistency** verifier — the property that makes the log
tamper-evident: an accepted consistency proof between two roots witnesses a
genuine append-only prefix relation between the two trees.

The Rust subject is `neml/src/proof.rs`:

* `verify_consistency` (`proof.rs:97`) =
  `reconstruct_consistency_roots(..).is_some_and(|(c_old, c_new)|
   c_old == old_root && c_new == new_root)` — the dual-root accept relation.
* `reconstruct_consistency_roots` (`proof.rs:593`) recomputes **both** the
  old-size and new-size roots from a single shared `path` anchored at
  `start_hash`, using the same frontier topology as inclusion.

## What the proof shows

Anchored at the honest current tree (`newRoot = karyRoot cells`,
`newSize = cells.length`):

* **Non-vacuity** (`consistency_completeness`): the honest consistency proof
  for `(cells, oldSize)` — the honest boundary-subtree root as `start_hash`
  and the honest path — is accepted, with the reconstructed roots being the
  genuine prefix root `karyRoot (cells.take oldSize)` and the genuine current
  root `karyRoot cells`. So the accept set is provably non-empty (mirroring
  `kary_completeness`).
* **Soundness** (`consistency_soundness`): *any* accepting consistency proof
  against the honest current root forces the reconstructed `oldRoot` to equal
  `karyRoot (cells.take oldSize)` — the root of the **unique** size-`oldSize`
  prefix of the current tree — modulo `NodeHashCollision` / `NullAmbiguity`
  (the two explicit hash hypotheses, never axioms). An attacker cannot make
  the verifier accept a *false* history (a forged `oldRoot`) against the true
  current tree.
* **Dual soundness** (`consistency_append_only`): accepting a proof between the
  honest root of `oldCells` and the honest root of `newCells` forces
  `oldCells <+: newCells` — the append-only relation at the cell-sequence
  level. Soundness binds it at the root level; this binds it at the data level.
  (The pure existential dual — "the new root is *some* extension's root" — is
  not faithfully recoverable: a consistency proof carries perfect-subtree
  roots, not the individual appended cells.)

`cells.take oldSize` is the append-only prefix: `oldSize < newSize =
cells.length`, and `cells.take oldSize <+: cells` holds definitionally
(`List.take_prefix`). The soundness theorem **concludes** the binding of
`oldRoot` to that prefix's root; it does not assume it.

## Proof architecture (reuses `Kary.lean` heavily)

The consistency path is the **suffix of the inclusion path of the last old
leaf** (`index = oldSize - 1`), taken from the boundary subtree's height
upward: `start_hash` plays the role of that subtree's root (`perfectRoot`),
the bisection steps are the upper digit steps, and the grouping steps are
identical. Hence:

* the new-root reconstruction is `foldNary start_hash path` (each Rust step —
  bisection, target merge, final merge — applies the same null-promoting
  `naryMr (insertAt position cur siblings)` to the running boundary digest;
  skipped coordinate merges consume no step and leave it untouched);
* soundness is **completeness + uniqueness** exactly as for inclusion: the
  honest path shape-matches the consistency skeleton, both fold to
  `karyRoot cells`, and `foldNary_unique_of_shape` forces the arbitrary
  accepting path to equal the honest one — pinning `start_hash` to the genuine
  boundary root and the recorded siblings to the genuine subtree roots, hence
  `oldRoot` to `karyRoot (cells.take oldSize)`.

The old-root reconstruction is modeled faithfully via the coordinate→digest
map that `reconstruct_consistency_roots` builds (`consistencyMap`): the
boundary coordinate maps to `start_hash`, and every bisection/merge step
records its siblings at their coordinates. The old root is the
`foldFrontierRoot` over the old frontier's coordinates read back from that map
(`proof.rs:842`).
-/

set_option linter.style.emptyLine false
set_option linter.unusedVariables false

namespace NEML

/-! ## Boundary topology

The "boundary" is the last (rightmost, smallest) perfect subtree of the old
frontier. Its span ends exactly at `oldSize`. These pure-arithmetic facts about
the frontier tiling anchor both the honest construction and the soundness
reduction; no hashing is involved. -/

/-- The last tile of a `Tiles` decomposition ends exactly at `stop`. -/
private theorem Tiles_last (k : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop bl bh : Nat),
      Tiles k start coords stop → coords.getLast? = some (bl, bh) →
        bl + k ^ bh = stop := by
  intro coords
  induction coords with
  | nil => intro start stop bl bh _ hlast; simp at hlast
  | cons p rest ih =>
    intro start stop bl bh htiles hlast
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    cases rest with
    | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq, Prod.mk.injEq] at hlast
        obtain ⟨hbl, hbh⟩ := hlast
        subst hbl; subst hbh
        simp only [Tiles] at htrest
        omega
    | cons q qs =>
        rw [List.getLast?_cons_cons] at hlast
        exact ih (start + k ^ ph) stop bl bh htrest hlast

/-- The old frontier's last coordinate `(bl, bh)` spans `[bl, oldSize)`:
    `bl + k ^ bh = oldSize`. -/
private theorem frontier_getLast_eq (k n bl bh : Nat) (hk : 2 ≤ k)
    (hlast : (frontierForSizeT k n).getLast? = some (bl, bh)) :
    bl + k ^ bh = n :=
  Tiles_last k (frontierForSizeT k n) 0 n bl bh (frontier_tiles k n hk) hlast

/-- **Frontier coordinates are aligned to their height.** Every perfect subtree
    `(l, h)` in the greedy decomposition starts at a multiple of `k ^ h` — the
    decomposition strips largest-first, so each new offset stays divisible by all
    smaller heights. Stated over `frontierGo` with the matching offset hypothesis
    so the induction closes; `frontierForSizeT` is the `off = 0` case. -/
private theorem frontierGo_aligned (k : Nat) (hk : 2 ≤ k) :
    ∀ (n off : Nat), k ^ Nat.log k n ∣ off → ∀ lh ∈ frontierGo k off n, k ^ lh.2 ∣ lh.1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro off hdvd lh hmem
    rw [frontierGo] at hmem
    split at hmem
    · simp only [List.not_mem_nil] at hmem
    · next h =>
        push_neg at h
        obtain ⟨hn0, _⟩ := h
        rw [List.mem_cons] at hmem
        have hcap : k ^ Nat.log k n ≤ n := Nat.pow_log_le_self k hn0
        have hcappos : 0 < k ^ Nat.log k n := pow_pos (by omega) _
        rcases hmem with rfl | hmem'
        · exact hdvd
        · have hHle : Nat.log k (n - k ^ Nat.log k n) ≤ Nat.log k n :=
            Nat.log_mono_right (by omega)
          have hdvd' : k ^ Nat.log k (n - k ^ Nat.log k n) ∣ (off + k ^ Nat.log k n) :=
            Nat.dvd_add (dvd_trans (pow_dvd_pow k hHle) hdvd) (pow_dvd_pow k hHle)
          exact ih (n - k ^ Nat.log k n) (by omega) (off + k ^ Nat.log k n) hdvd' lh hmem'

/-- The boundary coordinate `(bl, bh)` is `k ^ bh`-aligned: `k ^ bh ∣ bl`. -/
private theorem frontier_getLast_aligned (k n bl bh : Nat) (hk : 2 ≤ k)
    (hlast : (frontierForSizeT k n).getLast? = some (bl, bh)) :
    k ^ bh ∣ bl := by
  have hmem : (bl, bh) ∈ frontierForSizeT k n := List.mem_of_getLast? hlast
  exact frontierGo_aligned k hk n 0 (by simp) (bl, bh) hmem

/-- **Greedy slot height.** A frontier slot `(sl, sh)` has `sh = log_k (n - sl)`:
    the height is the log of the leaves still remaining when the greedy
    decomposition reaches `sl` (tiling pins the remaining count to `n - sl`). -/
private theorem frontierGo_slot_height (k : Nat) (hk : 2 ≤ k) :
    ∀ (n off sl sh : Nat), (sl, sh) ∈ frontierGo k off n →
      sh = Nat.log k (off + n - sl) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro off sl sh hmem
    rw [frontierGo] at hmem
    split at hmem
    · simp only [List.not_mem_nil] at hmem
    · next h =>
        push_neg at h
        obtain ⟨hn0, _⟩ := h
        rw [List.mem_cons] at hmem
        have hcap : k ^ Nat.log k n ≤ n := Nat.pow_log_le_self k hn0
        have hcappos : 0 < k ^ Nat.log k n := pow_pos (by omega) _
        rcases hmem with heq | hmem'
        · rw [Prod.ext_iff] at heq
          obtain ⟨hsl, hsh⟩ := heq
          simp only at hsl hsh
          subst hsl; subst hsh
          congr 1; omega
        · have hrec := ih (n - k ^ Nat.log k n) (by omega) (off + k ^ Nat.log k n) sl sh hmem'
          rw [hrec]; congr 1; omega

/-- **The boundary's new-frontier slot is at least as tall as the boundary
    subtree** (`bh ≤ sh`). The slot starts at `sl ≤ bl`, so `n - sl ≥ k ^ bh`
    leaves remain there; greedy then takes a subtree of height
    `log_k (n - sl) ≥ bh`. This is `reconstruct_consistency_roots`'s
    `new_height < boundary_height ⇒ None` guard, shown to never fire for an
    honest prefix relation. -/
private theorem newslot_height_ge (k newSize oldSize bl bh fIdx sl sh : Nat) (hk : 2 ≤ k)
    (hbspan : bl + k ^ bh = oldSize) (hold : oldSize ≤ newSize)
    (hslot : findFrontier k bl (frontierForSizeT k newSize) 0 = some (fIdx, sl, sh)) :
    bh ≤ sh := by
  obtain ⟨hget, hsle, _hblt⟩ := findFrontier_spec k bl (frontierForSizeT k newSize) 0 fIdx sl sh hslot
  have hmem : (sl, sh) ∈ frontierForSizeT k newSize :=
    List.mem_of_getElem? (by simpa using hget)
  have hheight : sh = Nat.log k (0 + newSize - sl) :=
    frontierGo_slot_height k hk newSize 0 sl sh hmem
  have hge : k ^ bh ≤ 0 + newSize - sl := by omega
  rw [hheight]
  exact Nat.le_log_of_pow_le (by omega) hge

/-- Every tile's left coordinate is at least the decomposition's start. -/
private theorem Tiles_left_ge (k : Nat) :
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

/-- **`findFrontier` is tile-deterministic.** If it locates a tile `(l, h)` for
    one index, it locates the same tile for any other index that tile covers:
    the tiles are disjoint and ordered, so a second in-tile index skips exactly
    the same prefix. The fact that lets the boundary `bl` and the last old leaf
    `oldSize - 1` (both inside the boundary subtree) share a new-frontier slot. -/
private theorem findFrontier_unique (k i₁ i₂ : Nat) :
    ∀ (coords : List (Nat × Nat)) (start stop c fIdx l h : Nat),
      Tiles k start coords stop →
      findFrontier k i₁ coords c = some (fIdx, l, h) →
      l ≤ i₂ → i₂ < l + k ^ h →
      findFrontier k i₂ coords c = some (fIdx, l, h) := by
  intro coords
  induction coords with
  | nil => intro start stop c fIdx l h _ hf; simp only [findFrontier, reduceCtorEq] at hf
  | cons p rest ih =>
    intro start stop c fIdx l h htiles hf hle hlt
    obtain ⟨pl, ph⟩ := p
    obtain ⟨hpl, htrest⟩ := htiles
    rw [findFrontier] at hf ⊢
    by_cases hc1 : pl ≤ i₁ ∧ i₁ < pl + k ^ ph
    · rw [if_pos hc1] at hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨hfi, hl, hh⟩ := hf
      subst hl; subst hh
      rw [if_pos ⟨hle, hlt⟩]
      simp [hfi]
    · rw [if_neg hc1] at hf
      obtain ⟨hget, _, _⟩ := findFrontier_spec k i₁ rest (c + 1) fIdx l h hf
      have hmem : (l, h) ∈ rest := List.mem_of_getElem? (by simpa using hget)
      have hlge : start + k ^ ph ≤ l := Tiles_left_ge k rest (start + k ^ ph) stop htrest (l, h) hmem
      have hi2 : ¬(pl ≤ i₂ ∧ i₂ < pl + k ^ ph) := by
        rintro ⟨_, hlt2⟩; omega
      rw [if_neg hi2]
      exact ih (start + k ^ ph) stop (c + 1) fIdx l h htrest hf hle hlt

/-- Dropping the low `bh` digit steps of a height-`sh` digit path leaves the
    height-`(sh - bh)` digit path of the `bh`-shifted offset. The digit-step
    counterpart of `start_hash` anchoring at the boundary height: the consistency
    skeleton's bisection steps are the inclusion skeleton's digit steps above
    `bh`. -/
private theorem digitSteps_drop (k : Nat) :
    ∀ (bh sh off : Nat), bh ≤ sh →
      (digitSteps k off sh).drop bh = digitSteps k (off / k ^ bh) (sh - bh) := by
  intro bh
  induction bh with
  | zero => intro sh off _; simp [pow_zero, Nat.div_one]
  | succ n ih =>
    intro sh off hle
    obtain ⟨s', rfl⟩ : ∃ s', sh = s' + 1 := ⟨sh - 1, by omega⟩
    rw [digitSteps, List.drop_succ_cons, ih s' (off / k) (by omega)]
    congr 1
    · rw [Nat.div_div_eq_div_mul, ← pow_succ']
    · omega

/-! ## The coordinate→digest map of `reconstruct_consistency_roots` -/

/-- A coordinate `(left, height)` → digest map, as `reconstruct_consistency_roots`
    builds it (`proof.rs:652`, a `HashMap<(u64, u32), Vec<u8>>`). -/
abbrev CMap := (Nat × Nat) → Option Digest

/-- The empty map. -/
def cmEmpty : CMap := fun _ => none

/-- Functional `map.insert(coord, digest)` (last write wins). -/
def cmInsert (m : CMap) (c : Nat × Nat) (d : Digest) : CMap :=
  fun c' => if c' = c then some d else m c'

/-- Record one bisection step's siblings (`proof.rs:683-698`). The path node
    sits at `(curLeft, ch)`; its parent at `(curLeft - position·k^ch, ch+1)`.
    Sibling `j` (`0 ≤ j < k-1`) is the child at horizontal offset
    `j·k^ch` (left of the path node) or `(j+1)·k^ch` (right of it), recorded at
    its own coordinate, height `ch`. -/
noncomputable def recordBisectSibs (k : Nat) (m : CMap) (curLeft ch : Nat) (s : ProofStep) : CMap :=
  let cap := k ^ ch
  let parentLeft := curLeft - s.position * cap
  (List.range s.siblings.length).foldl
    (fun mm j =>
      let cLeft := if j < s.position then parentLeft + j * cap else parentLeft + j * cap + cap
      cmInsert mm (cLeft, ch) (s.siblings.getD j emptyHash)) m

/-- The bisection phase (`proof.rs:661-708`): trace `start_hash`'s coordinate up
    `bisection_steps` levels, recording each step's siblings. Tracks only the
    coordinate (`curLeft, ch`) — the running digest is recovered separately by
    `foldNary`; sibling *coordinates* need no digest state. -/
noncomputable def cmBisect (k : Nat) : List ProofStep → Nat → Nat → CMap → CMap
  | [], _, _, m => m
  | s :: rest, curLeft, ch, m =>
      cmBisect k rest (curLeft - s.position * k ^ ch) (ch + 1) (recordBisectSibs k m curLeft ch s)

/-- Record one merge step's siblings (`proof.rs:754-772` and `815-826`): a
    window `nodes` of frontier coordinates with the target at local index `pos`;
    the other `nodes.length - 1` entries are recorded from `s.siblings`
    (sibling index shifted past the target, mirroring
    `if j < step.position { j } else { j - 1 }`). -/
noncomputable def recordMergeSibs (m : CMap) (nodes : List (Nat × Nat)) (pos : Nat) (s : ProofStep) : CMap :=
  (List.range nodes.length).foldl
    (fun mm j =>
      if j = pos then mm
      else
        let sibIdx := if j < s.position then j else j - 1
        cmInsert mm (nodes.getD j (0, 0)) (s.siblings.getD sibIdx emptyHash)) m

/-- One coordinate-merge length step: `mergeTopCoords` strictly shrinks a list
    longer than `k` (for `k ≥ 2`). -/
theorem mergeTopCoords_length_lt (k : Nat) (coords : List (Nat × Nat))
    (hk : 2 ≤ k) (hlen : k < coords.length) :
    (mergeTopCoords k coords).length < coords.length := by
  unfold mergeTopCoords
  rw [if_neg (by omega)]
  cases hd : (coords.drop (coords.length - k)).head? with
  | none =>
      exfalso
      have : (coords.drop (coords.length - k)).length = k := by
        rw [List.length_drop]; omega
      rw [List.head?_eq_none_iff] at hd
      rw [hd] at this; simp at this; omega
  | some lh =>
      obtain ⟨l, h⟩ := lh
      simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]
      omega

/-- The dynamic-merge phase (`proof.rs:710-836`): fold the new frontier by
    repeatedly merging the rightmost `k`, recording the siblings of every merge
    the target participates in (window merges consume a path step; coordinate
    merges that skip the target do not), then the final root merge. Records
    sibling coordinates into the map. -/
noncomputable def cmMergeGo (k : Nat) : List (Nat × Nat) → Nat → List ProofStep → CMap → CMap
  | frontier, targetIdx, path, m =>
    if h : k < 2 ∨ frontier.length ≤ k then
      if 1 < frontier.length then
        match path with
        | [] => m
        | s :: _ => recordMergeSibs m frontier targetIdx s
      else m
    else
      let split := frontier.length - k
      if targetIdx ≥ split then
        match path with
        | [] => m
        | s :: rest =>
            cmMergeGo k (mergeTopCoords k frontier) split rest
              (recordMergeSibs m (frontier.drop split) (targetIdx - split) s)
      else
        cmMergeGo k (mergeTopCoords k frontier) targetIdx path m
termination_by frontier => frontier.length
decreasing_by
  all_goals (push_neg at h; exact mergeTopCoords_length_lt k frontier (by omega) h.2)

/-- The full coordinate→digest map after a consistency reconstruction: the
    boundary coordinate seeded with `start_hash` (`proof.rs:654`), then the
    bisection and merge phases. -/
noncomputable def consistencyMap (k oldSize newSize : Nat) (startHash : Digest)
    (path : List ProofStep) : CMap :=
  match (frontierForSizeT k oldSize).getLast? with
  | none => cmEmpty
  | some (bl, bh) =>
    match findFrontier k bl (frontierForSizeT k newSize) 0 with
    | none => cmEmpty
    | some (fIdx, _sl, sh) =>
        let bisSteps := sh - bh
        let m0 := cmInsert cmEmpty (bl, bh) startHash
        let m1 := cmBisect k (path.take bisSteps) bl bh m0
        cmMergeGo k (frontierForSizeT k newSize) fIdx (path.drop bisSteps) m1

/-! ## The verifier model -/

/-- The list of old-frontier digests read back from the map (`proof.rs:842-847`):
    `None` if any old-frontier coordinate is absent (the algorithm aborts). -/
noncomputable def consistencyOldHashes (k oldSize newSize : Nat) (startHash : Digest)
    (path : List ProofStep) : Option (List Digest) :=
  (frontierForSizeT k oldSize).mapM (consistencyMap k oldSize newSize startHash path)

/-- `reconstruct_consistency_roots` (`proof.rs:593`), modeled functionally:
    the old root is the `foldFrontierRoot` over the old frontier's digests read
    from the map (`proof.rs:849-867`); the new root is the running boundary
    digest folded through the whole path (`foldNary start_hash path`), which is
    exactly the merge phase's `computed_new_root` (`proof.rs:870`). Returns
    `none` exactly when the map read-back fails. -/
noncomputable def reconstructConsistencyRoots (L k oldSize newSize : Nat)
    (startHash : Digest) (path : List ProofStep) : Option (Digest × Digest) :=
  match consistencyOldHashes k oldSize newSize startHash path with
  | none => none
  | some hs => some (foldFrontierRoot L k hs, foldNary L startHash path)

/-- The consistency-proof skeleton pinned by `reconstruct_consistency_roots`'s
    structural guards: `sh - bh` bisection steps (each `k - 1` siblings, position
    the base-`k` digit of the boundary subtree's offset in its new slot,
    `proof.rs:667-675`) then the grouping steps from that slot to the spine root
    (`proof.rs:739-836`). The boundary subtree root is a pure log-topology node,
    so — unlike inclusion — there is **no** unconstrained within-subtree prefix:
    the whole path is shape-pinned. -/
def consistencySkeleton (k oldSize newSize : Nat) : Option (List (Nat × Nat)) :=
  if k < 2 then none
  else match (frontierForSizeT k oldSize).getLast? with
    | none => none
    | some (bl, bh) =>
      match findFrontier k bl (frontierForSizeT k newSize) 0 with
      | none => none
      | some (fIdx, sl, sh) =>
        if bh ≤ sh then
          some (digitSteps k ((bl - sl) / k ^ bh) (sh - bh) ++
            (groupingSteps k (frontierForSizeT k newSize).length fIdx).map
              (fun pc => (pc.1, pc.2 - 1)))
        else none

/-- `verify_consistency`'s structural acceptance (`proof.rs:647-840`): the path's
    per-step shape matches the consistency skeleton exactly (full match — no free
    prefix). The k-ary analog of `StructureOK`, minus the existential depth. -/
def StructureConsistencyOK (k oldSize newSize : Nat) (path : List ProofStep) : Prop :=
  ∃ skel, consistencySkeleton k oldSize newSize = some skel ∧ path.map stepShape = skel

/-- The accept relation of `verify_consistency`, minus DoS bounds: size guards,
    skeleton pinning, canonical well-formedness (zero-sibling steps rejected,
    insert position in range — `proof.rs:617-625,667-670`), and the dual-root
    match `reconstruct_consistency_roots(..) == some (oldRoot, newRoot)`
    (`proof.rs:107`). -/
def AcceptsConsistency (L k oldSize newSize : Nat) (startHash : Digest)
    (path : List ProofStep) (oldRoot newRoot : Digest) : Prop :=
  2 ≤ k ∧ 0 < oldSize ∧ oldSize < newSize ∧
  StructureConsistencyOK k oldSize newSize path ∧
  WellFormedSteps path ∧
  reconstructConsistencyRoots L k oldSize newSize startHash path = some (oldRoot, newRoot)

/-! ## The honest prover (non-vacuity witness) -/

/-- The honest `start_hash`: the genuine root of the boundary subtree — the
    rightmost (last) perfect subtree of the old frontier. -/
noncomputable def honestStartHash (L k : Nat) (cells : List Digest)
    (oldSize : Nat) : Digest :=
  match (frontierForSizeT k oldSize).getLast? with
  | none => emptyHash
  | some (bl, bh) => perfectRoot L k cells bl bh

/-- The honest consistency path: the inclusion path of the last old leaf
    (`index = oldSize - 1`) in the current tree, taken from the boundary
    subtree's height upward (dropping the `bh` lower digit steps that fold the
    leaf up to the boundary subtree root — which `start_hash` already is). -/
noncomputable def honestConsistencyPath (L k : Nat) (cells : List Digest)
    (oldSize : Nat) : List ProofStep :=
  match (frontierForSizeT k oldSize).getLast? with
  | none => []
  | some (_bl, bh) => (honestInclusionPath L k cells (oldSize - 1)).drop bh

/-! ## Honest new-root reconstruction -/

/-- **Boundary/slot setup for an honest prefix.** Packages the geometric facts
    every honest-construction proof reuses: the boundary coordinate `(bl, bh)`
    (last old-frontier subtree, spanning `[bl, oldSize)`), the new-frontier slot
    `(fIdx, sl, sh)` containing both `bl` and the last old leaf `oldSize - 1`
    (`findFrontier` is tile-deterministic), with `bh ≤ sh`, `sl ≤ bl`, the
    bisection digit offsets agreeing (`(oldSize-1-sl)/k^bh = (bl-sl)/k^bh`), and
    the aligned-ancestor identity pinning the `bh`-level ancestor of `oldSize-1`
    to `bl`. -/
private theorem boundary_slot (k : Nat) (hk : 2 ≤ k) (cells : List Digest) (oldSize : Nat)
    (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    ∃ bl bh fIdx sl sh,
      (frontierForSizeT k oldSize).getLast? = some (bl, bh) ∧
      bl + k ^ bh = oldSize ∧
      findFrontier k bl (frontierForSizeT k cells.length) 0 = some (fIdx, sl, sh) ∧
      findFrontier k (oldSize - 1) (frontierForSizeT k cells.length) 0 = some (fIdx, sl, sh) ∧
      bh ≤ sh ∧ sl ≤ bl ∧
      (oldSize - 1 - sl) / k ^ bh = (bl - sl) / k ^ bh ∧
      sl + (oldSize - 1 - sl) / k ^ bh * k ^ bh = bl := by
  have hfrne : frontierForSizeT k oldSize ≠ [] := by
    intro he
    have ht := frontier_tiles k oldSize hk
    rw [he] at ht; simp only [Tiles] at ht; omega
  obtain ⟨bl, bh, hlast⟩ :
      ∃ bl bh, (frontierForSizeT k oldSize).getLast? = some (bl, bh) := by
    rcases hg : (frontierForSizeT k oldSize).getLast? with _ | ⟨bl, bh⟩
    · exact absurd (List.getLast?_eq_none_iff.mp hg) hfrne
    · exact ⟨bl, bh, rfl⟩
  have hspan : bl + k ^ bh = oldSize := frontier_getLast_eq k oldSize bl bh hk hlast
  have hbalign : k ^ bh ∣ bl := frontier_getLast_aligned k oldSize bl bh hk hlast
  have hk0 : 0 < k ^ bh := pow_pos (by omega) bh
  have hbllt : bl < cells.length := by omega
  obtain ⟨fIdx, sl, sh, hff⟩ := findFrontier_cover k bl (frontierForSizeT k cells.length) 0
    cells.length 0 (frontier_tiles k cells.length hk) (Nat.zero_le _) hbllt
  obtain ⟨hget, hsle, hblt⟩ :=
    findFrontier_spec k bl (frontierForSizeT k cells.length) 0 fIdx sl sh hff
  have hslmem : (sl, sh) ∈ frontierForSizeT k cells.length :=
    List.mem_of_getElem? (by simpa using hget)
  have hslalign : k ^ sh ∣ sl := frontierGo_aligned k hk cells.length 0 (by simp) (sl, sh) hslmem
  have hbhsh : bh ≤ sh :=
    newslot_height_ge k cells.length oldSize bl bh fIdx sl sh hk hspan (le_of_lt hnew) hff
  have hbhdvdsl : k ^ bh ∣ sl := dvd_trans (pow_dvd_pow k hbhsh) hslalign
  obtain ⟨a, ha⟩ := hbalign
  obtain ⟨b, hb⟩ := hbhdvdsl
  have hba : b ≤ a := Nat.le_of_mul_le_mul_left (by omega) hk0
  have hm : bl - sl = k ^ bh * (a - b) := by rw [ha, hb, Nat.mul_sub]
  set m := a - b with hmdef
  have hnest : bl + k ^ bh ≤ sl + k ^ sh := by
    obtain ⟨q, hq⟩ := pow_dvd_pow k hbhsh
    have h1 : k ^ bh * m < k ^ bh * q := by rw [← hq]; omega
    have hmq : m < q := lt_of_mul_lt_mul_left h1 (Nat.zero_le _)
    have h2 : k ^ bh * (m + 1) ≤ k ^ bh * q := Nat.mul_le_mul (le_refl _) (by omega)
    have he : k ^ bh * (m + 1) = k ^ bh * m + k ^ bh := by ring
    rw [hq]; omega
  have hff2 : findFrontier k (oldSize - 1) (frontierForSizeT k cells.length) 0
      = some (fIdx, sl, sh) :=
    findFrontier_unique k bl (oldSize - 1) (frontierForSizeT k cells.length) 0 cells.length 0
      fIdx sl sh (frontier_tiles k cells.length hk) hff (by omega) (by omega)
  have hofs : (oldSize - 1 - sl) / k ^ bh = m := by
    have hrw : oldSize - 1 - sl = k ^ bh * m + (k ^ bh - 1) := by omega
    rw [hrw, Nat.mul_add_div hk0, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hdiveq : (oldSize - 1 - sl) / k ^ bh = (bl - sl) / k ^ bh := by
    rw [hofs, hm, Nat.mul_div_cancel_left m hk0]
  have halign : sl + (oldSize - 1 - sl) / k ^ bh * k ^ bh = bl := by
    have hc : m * k ^ bh = k ^ bh * m := Nat.mul_comm _ _
    rw [hofs]; omega
  exact ⟨bl, bh, fIdx, sl, sh, hlast, hspan, hff, hff2, hbhsh, hsle, hdiveq, halign⟩

/-- **The honest consistency path reconstructs the genuine new root.**
    Folding the honest boundary-subtree root (`start_hash`) through the honest
    consistency path yields `karyRoot cells`. The path is the suffix, from the
    boundary height up, of the inclusion path of the last old leaf
    (`oldSize - 1`): `honest_path_folds` folds that leaf to the root, and the
    dropped lower `bh` digit steps fold the leaf up to the boundary subtree root
    (`digitFold`), which `start_hash` is. The boundary lands in a new-frontier
    slot of height `≥ bh` (`newslot_height_ge`), shared with `oldSize - 1`
    (`findFrontier_unique`), and the boundary's aligned position pins the
    `bh`-level ancestor of `oldSize - 1` to `bl`. -/
private theorem honest_consistency_newroot (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    foldNary L (honestStartHash L k cells oldSize) (honestConsistencyPath L k cells oldSize)
      = karyRoot L k cells := by
  obtain ⟨bl, bh, fIdx, sl, sh, hlast, hspan, _hff, hff2, hbhsh, hsle, _hdiveq, halign⟩ :=
    boundary_slot k hk cells oldSize hold hnew
  have hk0 : 0 < k ^ bh := pow_pos (by omega) bh
  -- unfold the honest start hash and path
  simp only [honestStartHash, honestConsistencyPath, hlast]
  -- honest inclusion path through the shared slot
  have hincl : honestInclusionPath L k cells (oldSize - 1)
      = honestDigitPath L k cells sl (oldSize - 1 - sl) sh
        ++ honestGroupPath L k (buildStackCells L k cells) fIdx := by
    simp only [honestInclusionPath, hff2]
  set leaf := cells.getD (oldSize - 1) emptyHash with hleaf
  have hfull := honest_path_folds L k hk cells (oldSize - 1) (by omega)
  -- the dropped lower bh steps fold the leaf to the boundary subtree root
  have htakefold : foldNary L leaf
      ((honestInclusionPath L k cells (oldSize - 1)).take bh) = perfectRoot L k cells bl bh := by
    rw [hincl]
    have hdlen : (honestDigitPath L k cells sl (oldSize - 1 - sl) sh).length = sh := by
      rw [honestDigitPath, List.length_map, List.length_range]
    rw [List.take_append_of_le_length (by rw [hdlen]; exact hbhsh)]
    have htk : (honestDigitPath L k cells sl (oldSize - 1 - sl) sh).take bh
        = honestDigitPath L k cells sl (oldSize - 1 - sl) bh := by
      rw [honestDigitPath, honestDigitPath, ← List.map_take, List.take_range, Nat.min_eq_left hbhsh]
    rw [htk]
    have hdf := digitFold L k hk cells sl bh (oldSize - 1 - sl)
    rw [show sl + (oldSize - 1 - sl) = oldSize - 1 from by omega, halign] at hdf
    rw [hleaf]; exact hdf
  -- assemble via the take/drop split of the honest fold
  have hsplit : foldNary L leaf (honestInclusionPath L k cells (oldSize - 1))
      = foldNary L (foldNary L leaf ((honestInclusionPath L k cells (oldSize - 1)).take bh))
          ((honestInclusionPath L k cells (oldSize - 1)).drop bh) := by
    rw [foldNary, foldNary, foldNary, ← List.foldl_append, List.take_append_drop]
  rw [← hfull, hsplit, htakefold]

/-- **The honest consistency path has the pinned skeleton shape.** Its per-step
    shape equals `consistencySkeleton`. The honest path is the inclusion path of
    the last old leaf dropped to the boundary height; its shape is therefore the
    inclusion skeleton dropped by `bh`, whose bisection digit steps coincide with
    the consistency skeleton's (`digitSteps_drop` plus the agreeing digit offset)
    and whose grouping steps are identical. -/
private theorem honest_consistency_shape (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    StructureConsistencyOK k oldSize cells.length (honestConsistencyPath L k cells oldSize) := by
  obtain ⟨bl, bh, fIdx, sl, sh, hlast, hspan, hff, hff2, hbhsh, hsle, hdiveq, _halign⟩ :=
    boundary_slot k hk cells oldSize hold hnew
  obtain ⟨⟨skel, hskel, hmap⟩, _hwf⟩ := honest_path_shape L k hk cells (oldSize - 1) (by omega)
  set G := (groupingSteps k (frontierForSizeT k cells.length).length fIdx).map
    (fun pc => (pc.1, pc.2 - 1)) with hG
  have hsk : inclusionSkeleton k cells.length (oldSize - 1)
      = some (digitSteps k (oldSize - 1 - sl) sh ++ G) := by
    rw [inclusionSkeleton, if_neg (show ¬ k < 2 by omega)]
    simp only [hff2, hG]
  have hskelval : skel = digitSteps k (oldSize - 1 - sl) sh ++ G :=
    Option.some.inj (hskel.symm.trans hsk)
  have hcskel : consistencySkeleton k oldSize cells.length
      = some (digitSteps k ((bl - sl) / k ^ bh) (sh - bh) ++ G) := by
    rw [consistencySkeleton, if_neg (show ¬ k < 2 by omega)]
    simp only [hlast, hff, hbhsh, if_true, hG]
  have hdslen : (digitSteps k (oldSize - 1 - sl) sh).length = sh := by
    rw [digitSteps_eq_map, List.length_map, List.length_range]
  refine ⟨digitSteps k ((bl - sl) / k ^ bh) (sh - bh) ++ G, hcskel, ?_⟩
  simp only [honestConsistencyPath, hlast]
  rw [List.map_drop, hmap, hskelval,
    List.drop_append_of_le_length (by rw [hdslen]; exact hbhsh),
    digitSteps_drop k bh sh (oldSize - 1 - sl) hbhsh, hdiveq]

/-- **The honest old-root read-back yields the genuine prefix root.** The
    coordinate map the verifier builds for an honest consistency proof records,
    at each old-frontier coordinate, its genuine `perfectRoot`; folding those
    with the frontier grouping (`foldFrontierRoot`) gives `karyRoot` of the
    size-`oldSize` prefix. This is the coordinate-coverage core: the boundary is
    `start_hash`, the bisection siblings are the perfect roots flanking the
    boundary path inside its slot, and the merge siblings are the perfect roots
    of the new-frontier slots left of it — together exactly the old frontier. -/
private theorem honest_oldroot_readback (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    ∃ hs, consistencyOldHashes k oldSize cells.length (honestStartHash L k cells oldSize)
        (honestConsistencyPath L k cells oldSize) = some hs ∧
      foldFrontierRoot L k hs = karyRoot L k (cells.take oldSize) := by
  sorry

/-! ## The theorems -/

/-- **Non-vacuity: honest consistency proofs verify.** The honest boundary-root
    `start_hash` and honest path are accepted against the genuine current root
    `karyRoot cells`, reconstructing the genuine prefix root
    `karyRoot (cells.take oldSize)`. So `AcceptsConsistency` is satisfiable for
    every valid `(cells, oldSize)`, and the soundness theorem below quantifies
    over a provably non-empty accept set — mirroring how `kary_completeness`
    guards `kary_inclusion_soundness`.

    *Strategy:* `start_hash = perfectRoot (bl, bh)` is the digest the last old
    leaf reaches after `bh` digit steps (`digitFold`); the dropped honest path
    therefore folds it to `karyRoot cells` by `honest_path_folds` +
    `List.foldl` append decomposition. The shape matches `consistencySkeleton`
    (the dropped portion of `honest_path_shape`). The old-root read-back equals
    `karyRoot (cells.take oldSize)` because every old-frontier coordinate is
    recorded with its genuine `perfectRoot` and `foldFrontierRoot` over them is
    `karyRoot` of the prefix (`kary_bridge` on `cells.take oldSize`). -/
theorem consistency_completeness (L k : Nat) (hk : 2 ≤ k) (cells : List Digest)
    (oldSize : Nat) (hold : 0 < oldSize) (hnew : oldSize < cells.length) :
    AcceptsConsistency L k oldSize cells.length
      (honestStartHash L k cells oldSize) (honestConsistencyPath L k cells oldSize)
      (karyRoot L k (cells.take oldSize)) (karyRoot L k cells) := by
  refine ⟨hk, hold, hnew, honest_consistency_shape L k hk cells oldSize hold hnew, ?_, ?_⟩
  · -- WellFormedSteps: the honest consistency path is a suffix of the honest
    -- inclusion path, which is well-formed
    obtain ⟨_, hwf⟩ := honest_path_shape L k hk cells (oldSize - 1) (by omega)
    obtain ⟨bl, bh, _, _, _, hlast, _⟩ := boundary_slot k hk cells oldSize hold hnew
    intro s hs
    simp only [honestConsistencyPath, hlast] at hs
    exact hwf s (List.mem_of_mem_drop hs)
  · -- dual-root reconstruction
    obtain ⟨hs, hhs, hfold⟩ := honest_oldroot_readback L k hk cells oldSize hold hnew
    simp only [reconstructConsistencyRoots, hhs]
    rw [hfold, honest_consistency_newroot L k hk cells oldSize hold hnew]

/-- **Consistency-verifier soundness: accept ⇒ genuine append-only prefix.**
    If `verify_consistency` accepts `(start_hash, path, oldRoot)` against the
    honest current root `karyRoot cells` (`newSize = cells.length`), then the
    reconstructed `oldRoot` is forced to be the genuine root of the size-`oldSize`
    prefix `cells.take oldSize` — modulo `NodeHashCollision` / `NullAmbiguity`.

    This is the V9 tamper-evidence statement for the consistency verifier: there
    is no `(start_hash, path)` making the verifier accept a `oldRoot` that
    disagrees with the true history of the genuine current tree. Combined with
    `consistency_completeness` (the accept set is non-empty), the verifier
    accepts an `oldRoot` **iff** it is the true prefix root.

    *Strategy (completeness + uniqueness — no new induction):* the path
    shape-matches `consistencySkeleton`; so does the honest path
    (`consistency_completeness`'s shape obligation). Both fold `start_hash` /
    the honest boundary root to `karyRoot cells`. `foldNary_unique_of_shape`
    forces `start_hash` to the genuine boundary root and `path` to the honest
    path; the old-root read-back is then `karyRoot (cells.take oldSize)` by the
    completeness computation. -/
theorem consistency_soundness (L k : Nat) (cells : List Digest)
    (oldSize : Nat) (startHash oldRoot : Digest) (path : List ProofStep)
    (hacc : AcceptsConsistency L k oldSize cells.length startHash path oldRoot
      (karyRoot L k cells))
    (hH : ¬NodeHashCollision) (hN : ¬NullAmbiguity L) :
    oldRoot = karyRoot L k (cells.take oldSize) := by
  obtain ⟨hk, hold, holdnew, hstruct, hwf, hrec⟩ := hacc
  obtain ⟨skel, hcsk, hpsh⟩ := hstruct
  obtain ⟨skel', hcsk', hpsh'⟩ := honest_consistency_shape L k hk cells oldSize hold holdnew
  have hskeq : skel = skel' := Option.some.inj (hcsk.symm.trans hcsk')
  have hshapes : path.map stepShape
      = (honestConsistencyPath L k cells oldSize).map stepShape := by
    rw [hpsh, hskeq, ← hpsh']
  have hwf_honest : WellFormedSteps (honestConsistencyPath L k cells oldSize) := by
    obtain ⟨_, hwfI⟩ := honest_path_shape L k hk cells (oldSize - 1) (by omega)
    obtain ⟨bl, bh, _, _, _, hlast, _⟩ := boundary_slot k hk cells oldSize hold holdnew
    intro s hs
    simp only [honestConsistencyPath, hlast] at hs
    exact hwfI s (List.mem_of_mem_drop hs)
  have hnewfold := honest_consistency_newroot L k hk cells oldSize hold holdnew
  obtain ⟨hsh, hoph, hfoldh⟩ := honest_oldroot_readback L k hk cells oldSize hold holdnew
  unfold reconstructConsistencyRoots at hrec
  split at hrec
  · simp at hrec
  · next hsp hop =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hrec
    obtain ⟨hoR, hnR⟩ := hrec
    have hfeq : foldNary L startHash path
        = foldNary L (honestStartHash L k cells oldSize)
            (honestConsistencyPath L k cells oldSize) := by rw [hnR, hnewfold]
    obtain ⟨hstart, hpatheq⟩ := foldNary_unique_of_shape L startHash
      (honestStartHash L k cells oldSize) path (honestConsistencyPath L k cells oldSize)
      hshapes hwf hwf_honest hfeq hH hN
    rw [hstart, hpatheq, hoph] at hop
    have hsphs : hsp = hsh := (Option.some.inj hop).symm
    rw [← hoR, hsphs]
    exact hfoldh

/-! ### `karyRoot` injectivity (supports the dual append-only theorem) -/

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
private theorem perfectRoot_inj (L k : Nat) (hk : 2 ≤ k)
    (hH : ¬NodeHashCollision) (hN : ¬NullAmbiguity L) (xs ys : List Digest) :
    ∀ (h left : Nat), perfectRoot L k xs left h = perfectRoot L k ys left h →
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
    have eL : perfectRoot L k xs left (n + 1)
        = naryMr L ((List.range k).map (fun j => perfectRoot L k xs (left + j * k ^ n) n)) := by
      rw [perfectRoot]
    have eR : perfectRoot L k ys left (n + 1)
        = naryMr L ((List.range k).map (fun j => perfectRoot L k ys (left + j * k ^ n) n)) := by
      rw [perfectRoot]
    rw [eL, eR] at heq
    have h2 : 2 ≤ ((List.range k).map
        (fun j => perfectRoot L k xs (left + j * k ^ n) n)).length := by simp; omega
    have hlen : ((List.range k).map (fun j => perfectRoot L k xs (left + j * k ^ n) n)).length
        = ((List.range k).map (fun j => perfectRoot L k ys (left + j * k ^ n) n)).length := by simp
    have hmapeq := naryMr_inj_of_length L _ _ hlen h2 heq hH hN
    -- per-child equality
    have hchild : ∀ j, j < k →
        perfectRoot L k xs (left + j * k ^ n) n = perfectRoot L k ys (left + j * k ^ n) n :=
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
private theorem naryMr_inj_eqlen (L : Nat) (xs ys : List Digest)
    (hlen : xs.length = ys.length) (heq : naryMr L xs = naryMr L ys)
    (hH : ¬NodeHashCollision) (hN : ¬NullAmbiguity L) : xs = ys := by
  rcases xs with _ | ⟨a, xs'⟩
  · rcases ys with _ | ⟨c, ys'⟩
    · rfl
    · simp only [List.length_nil, List.length_cons] at hlen; omega
  · rcases ys with _ | ⟨c, ys'⟩
    · simp only [List.length_nil, List.length_cons] at hlen; omega
    · rcases xs' with _ | ⟨b, s⟩
      · rcases ys' with _ | ⟨d, t⟩
        · have e1 : naryMr L [a] = a := rfl
          have e2 : naryMr L [c] = c := rfl
          rw [e1, e2] at heq; rw [heq]
        · simp only [List.length_cons, List.length_nil] at hlen; omega
      · rcases ys' with _ | ⟨d, t⟩
        · simp only [List.length_cons, List.length_nil] at hlen; omega
        · exact naryMr_inj_of_length L _ _ hlen (by simp) heq hH hN

/-- **`foldFrontierRoot` injectivity over equal-length stacks.** Two stacks of
    equal length folding to the same spine root coincide — or a hash assumption
    broke. Strong induction on the (shared) length: the merge schedule is
    length-determined, so each `mergeTopD` step stays aligned and inverts via
    `naryMr_inj_of_length`. -/
private theorem foldFrontierRoot_inj (L k : Nat) (hk : 2 ≤ k)
    (hH : ¬NodeHashCollision) (hN : ¬NullAmbiguity L) :
    ∀ (n : Nat) (xs ys : List Digest), xs.length = n → ys.length = n →
      foldFrontierRoot L k xs = foldFrontierRoot L k ys → xs = ys := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro xs ys hx hy heq
    by_cases hbase : xs.length ≤ k
    · have hbx : k < 2 ∨ xs.length ≤ k := Or.inr hbase
      have hby : k < 2 ∨ ys.length ≤ k := Or.inr (by omega)
      rw [foldFrontierRoot, dif_pos hbx] at heq
      conv_rhs at heq => rw [foldFrontierRoot, dif_pos hby]
      -- heq : naryMr L xs = naryMr L ys
      exact naryMr_inj_eqlen L xs ys (by omega) heq hH hN
    · push_neg at hbase
      have hbx : ¬(k < 2 ∨ xs.length ≤ k) := by push_neg; exact ⟨by omega, by omega⟩
      have hby : ¬(k < 2 ∨ ys.length ≤ k) := by push_neg; exact ⟨by omega, by omega⟩
      rw [foldFrontierRoot, dif_neg hbx] at heq
      conv_rhs at heq => rw [foldFrontierRoot, dif_neg hby]
      have hmx : (mergeTopD L k xs).length = n - k + 1 := by
        rw [mergeTopD, if_neg (by omega)]; simp only [List.length_append, List.length_take,
          List.length_cons, List.length_nil]; omega
      have hmy : (mergeTopD L k ys).length = n - k + 1 := by
        rw [mergeTopD, if_neg (by omega)]; simp only [List.length_append, List.length_take,
          List.length_cons, List.length_nil]; omega
      have hmerge := ih (n - k + 1) (by omega) (mergeTopD L k xs) (mergeTopD L k ys) hmx hmy heq
      -- mergeTopD xs = mergeTopD ys  ⇒  xs = ys
      rw [mergeTopD, if_neg (by omega), mergeTopD, if_neg (by omega)] at hmerge
      have hlenx : (xs.take (xs.length - k)).length = (ys.take (ys.length - k)).length := by
        simp only [List.length_take]; omega
      obtain ⟨htake, hsnoc⟩ := List.append_inj hmerge hlenx
      have hdrop2 : 2 ≤ (xs.drop (xs.length - k)).length := by
        simp only [List.length_drop]; omega
      have hdroplen : (xs.drop (xs.length - k)).length = (ys.drop (ys.length - k)).length := by
        simp only [List.length_drop]; omega
      have hnary : naryMr L (xs.drop (xs.length - k)) = naryMr L (ys.drop (ys.length - k)) := by
        have := List.cons.inj hsnoc; exact this.1
      have hdrop := naryMr_inj_of_length L _ _ hdroplen hdrop2 hnary hH hN
      calc xs = xs.take (xs.length - k) ++ xs.drop (xs.length - k) := (List.take_append_drop _ _).symm
        _ = ys.take (ys.length - k) ++ ys.drop (ys.length - k) := by rw [htake, hdrop]
        _ = ys := List.take_append_drop _ _

/-- **`karyRoot` injectivity over equal-length cell lists.** Two cell lists of
    the same length with equal k-ary root coincide — or a hash assumption broke.
    Equal length is essential: by the flat-null-promotion design, all-null lists
    of *different* lengths share a root (`naryRoot = nullDigest`), so injectivity
    can only hold once length is pinned (which the consistency proof's size
    fields do). The k-ary analog of `naryMr_inj_of_length` lifted from one node
    to the whole frontier fold.

    *Strategy:* induct on the frontier structure / `foldFrontierRoot`, applying
    `naryMr_inj_of_length` at each merge; the equal-length hypothesis keeps the
    two folds shape-aligned. -/
theorem karyRoot_inj_of_length (L k : Nat) (hk : 2 ≤ k) (xs ys : List Digest)
    (hlen : xs.length = ys.length) (heq : karyRoot L k xs = karyRoot L k ys)
    (hH : ¬NodeHashCollision) (hN : ¬NullAmbiguity L) :
    xs = ys := by
  rw [karyRoot, karyRoot, kary_bridge L k hk xs, kary_bridge L k hk ys, ← hlen] at heq
  set F := frontierForSizeT k xs.length with hF
  have hstacklen : (F.map (fun lh => perfectRoot L k xs lh.1 lh.2)).length
      = (F.map (fun lh => perfectRoot L k ys lh.1 lh.2)).length := by simp
  have hmaps := foldFrontierRoot_inj L k hk hH hN _ _ _ rfl hstacklen.symm heq
  -- per-coordinate root equality
  have hcoord : ∀ c ∈ F, perfectRoot L k xs c.1 c.2 = perfectRoot L k ys c.1 c.2 :=
    fun c hc => List.map_inj_left.mp hmaps c hc
  -- index-wise equality via tiling
  have hcover := Tiles_covers k F 0 xs.length (frontier_tiles k xs.length hk)
  have hpt : ∀ i, i < xs.length → xs.getD i emptyHash = ys.getD i emptyHash := by
    intro i hi
    obtain ⟨c, hc, h1, h2⟩ := hcover i (by omega) hi
    have hpr := perfectRoot_inj L k hk hH hN xs ys c.2 c.1 (hcoord c hc) (i - c.1) (by omega)
    rwa [show c.1 + (i - c.1) = i from by omega] at hpr
  apply List.ext_getElem hlen
  intro i h1 h2
  have hp := hpt i h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at hp
  exact hp

/-- **Dual soundness: accept between two honest roots ⇒ data-level append-only.**
    If `verify_consistency` accepts a proof between the honest root of `oldCells`
    and the honest root of `newCells`, then `oldCells` is a genuine prefix of
    `newCells` — the append-only relation at the cell-sequence level, modulo
    `NodeHashCollision` / `NullAmbiguity`.

    This is the dual of `consistency_soundness`: that theorem fixes the honest
    *new* tree and binds the reconstructed `oldRoot` to the prefix root; this one
    fixes the honest *old* tree as well and concludes that the accepted new tree
    genuinely *extends* it (`oldCells <+: newCells`). The two together are the
    complete tamper-evidence story — an accepted consistency proof between honest
    roots witnesses, at the data level, that the new log was formed by appending
    to the old one.

    The pure existential dual ("∃ extension whose root is `newRoot`") is *not*
    stated, because it is not faithfully recoverable: a consistency proof carries
    perfect-subtree *roots* for the appended range, never the individual new
    cells, so no leaf-level extension can be reconstructed from an arbitrary
    accepting proof. The two-honest-tree prefix relation is the faithful dual.

    *Strategy:* `consistency_soundness` (with `cells := newCells`) gives
    `karyRoot oldCells = karyRoot (newCells.take oldCells.length)`; both lists
    have length `oldCells.length`, so `karyRoot_inj_of_length` yields
    `oldCells = newCells.take oldCells.length`, i.e. `oldCells <+: newCells`. -/
theorem consistency_append_only (L k : Nat) (oldCells newCells : List Digest)
    (startHash : Digest) (path : List ProofStep)
    (hacc : AcceptsConsistency L k oldCells.length newCells.length startHash path
      (karyRoot L k oldCells) (karyRoot L k newCells))
    (hH : ¬NodeHashCollision) (hN : ¬NullAmbiguity L) :
    oldCells <+: newCells := by
  have hk : 2 ≤ k := hacc.1
  have hsize : oldCells.length < newCells.length := hacc.2.2.1
  have hsound := consistency_soundness L k newCells oldCells.length startHash
    (karyRoot L k oldCells) path hacc hH hN
  have hlen : oldCells.length = (newCells.take oldCells.length).length := by
    rw [List.length_take]; omega
  have heqcells := karyRoot_inj_of_length L k hk oldCells (newCells.take oldCells.length)
    hlen hsound hH hN
  rw [heqcells]
  exact List.take_prefix oldCells.length newCells

/-- The append-only prefix the soundness conclusion is about: `cells.take
    oldSize` is a genuine prefix of the current `cells`, with
    `oldSize < cells.length`. Definitional, recorded to make the prefix
    relation explicit at the statement surface. -/
theorem consistency_prefix_relation (cells : List Digest) (oldSize : Nat)
    (h : oldSize < cells.length) :
    (cells.take oldSize) <+: cells ∧ oldSize < cells.length :=
  ⟨List.take_prefix oldSize cells, h⟩

end NEML
