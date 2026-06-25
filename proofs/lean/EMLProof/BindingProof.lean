import EMLProof.Foundations
import EMLProof.Polydigest

/-!
# Binding-proof soundness (polydigest combinator, over `Foundations`)

The **binding proof** is the cross-algorithm peer of inclusion / consistency /
leaf / snapshot proofs (`polydigest/src/binding_proof.rs`). It proves that a set of
per-algorithm *binding roots* are mutually consistent: that every algorithm has
committed, under its **own** hash, to the *same* logical structure — the same
member-root tuple `ar` and the same committed epoch timeline `tl`.

## The per-algorithm binding root (no security mixing)

Each algorithm `i` carries its own hash `Hᵢ` and its own binding root

```text
BRᵢ = combinedRootWith Hᵢ ar tl
```

the canonicalization fold (`NEML.combinedRootWith`, mirroring `polydigest::combined_root`)
over the shared member roots as children, plus a coverage child iff the timeline
is non-trivial, **under `Hᵢ`**. Critically, `Hᵢ` is applied only to the shared
children; no other algorithm's binding root ever enters `Hᵢ`. This is design
decision **D9** — *no security mixing* — modelled by giving each algorithm an
*independent* hash `Hᵢ` as a parameter. The binding root's collision resistance
is `Hᵢ`'s alone, captured below as the discharged hypothesis
`¬ NodeHashCollisionFor Hᵢ`.

## What the fold changes vs. the old metaroot

The combined root is the raw-concat `nary_mr` fold over the member-root child
**bytes** (`Vec<u8>`, fed unprefixed — *not* re-hashed per member, the SEV-2b
fix), not the length-prefixed `H(metaPreimage)` byte string (N29). So a fixed
binding root pins the **member-root child-byte list** (and the coverage child)
modulo a byte-hash collision — *under the fixed-width contract* that makes the
unprefixed concat parseable (`EqWidth`, the code-side `Hasher::digest_len`
analogue, N32) — not the abstract `(ar, tl)` structure. Recovering the algorithm
*identities* is the verifier's trusted `expected_active_algs` input
(`active_roots.len() == expected_active_algs.len()`, here `hlen`), not something
the root re-establishes. Soundness is therefore stated over the member-byte list:
a presented structure inconsistent with what `i` committed cannot reproduce the
*children* (modulo collision, given equal width), so it is rejected.

## Trust base

This module adds **no axiom**. It is parameterized by the per-algorithm hashes
`Hᵢ` (ordinary function parameters) and reuses `NEML.combinedChildrenWith_bound`
— itself a hash-agnostic structural fact about the fold. Every theorem here
reports a `#print axioms` subset of the four `Foundations` axioms (`Digest`,
`Digest.nonempty`, `H`, `digestToBytes`) plus the Lean built-ins.

## What is proven

* `binding_root_sound` — *per-algorithm soundness*: if a presented structure
  `(ar', tl')` (same active-set length, equal-width children) produces algorithm
  `i`'s trusted binding root under `Hᵢ`, then it carries the *same member-root
  bytes* as what `i` genuinely committed, unless `Hᵢ`'s byte-hash collides.
* `binding_proof_consistent` — *cross-algorithm consistency*: if a single
  presented `(ar', tl')` verifies for **both** algorithms `i` and `j` (each over
  its own committed length and width), then the member-root byte lists they
  committed coincide with the presented one — the algorithms agree on the same
  member roots — unless one of the two independent hashes collides.
* `binding_proof_forgery_rejected` — *forgery rejection*: if the two algorithms
  committed **different** member-root child lists, no presented `(ar', tl')` can
  verify against both binding roots at once, unless a hash collides.
-/

namespace BindingProof

open NEML

/-- One algorithm's contribution to a binding proof: its own hash `hash` (`Hᵢ`)
    and the binding root `root` (`BRᵢ`) it is trusted to have published. The
    binding root is the raw `Vec<u8>` the Rust `nary_mr` returns (`List UInt8`).
    The structure it actually committed (`ar`, `tl`) is what soundness recovers. -/
structure Algorithm where
  /-- That algorithm's own hash `Hᵢ`. Applied only (at the node level) to the
      raw concatenation of the shared member-root children; never to another
      algorithm's binding root (D9). -/
  hash : List UInt8 → Digest
  /-- The trusted binding root `BRᵢ` this algorithm published (raw bytes). -/
  root : List UInt8

/-- The binding root algorithm `i` obtains for a structure `(ar, tl)`: the
    raw-concat canonicalization fold over the member-root children under its own
    hash. Mirrors `BindingProof::verify`, which recomputes `combined_root(Hᵢ, …)`
    per algorithm. -/
noncomputable def bindingRoot (alg : Algorithm)
    (ar : List (AlgId × List UInt8)) (tl : Timeline) : List UInt8 :=
  combinedRootWith alg.hash ar tl

/-- The verifier's per-algorithm accept relation: the presented structure
    `(ar', tl')` folds, under `alg`'s own hash, to `alg`'s trusted binding root.
    Mirrors the `constant_time_eq(combined_root(Hᵢ, …), BRᵢ)` check in `verify`. -/
def Verifies (alg : Algorithm)
    (ar' : List (AlgId × List UInt8)) (tl' : Timeline) : Prop :=
  bindingRoot alg ar' tl' = alg.root

/-- **Per-algorithm binding-root soundness (raw-concat fold model).** Let
    `(arᵢ, tlᵢ)` be the structure algorithm `i` genuinely committed under its
    binding root, both presented and committed in the multi-member regime (≥ 2
    member roots), over the same active-set length (`hlen`), and with equal-width
    children (`hw'`/`hw_i`, the `Hasher` fixed-width contract). If a presented
    `(ar', tl')` verifies against the same binding root, then it carries the
    *same member-root bytes* — `ar'.map (memberDigestWith alg.hash) = arᵢ.map
    (memberDigestWith alg.hash)`, `memberDigestWith` being the raw member bytes —
    unless `alg`'s own byte-hash collides. The committed member bytes are
    *derived* from the fold, never assumed. -/
theorem binding_root_sound {w : Nat} (alg : Algorithm)
    (ar_i ar' : List (AlgId × List UInt8)) (tl_i tl' : Timeline)
    (hmulti_i : ar_i.length ≥ 2) (hmulti' : ar'.length ≥ 2)
    (hlen : ar'.length = ar_i.length)
    (hw' : EqWidth w (combinedChildrenWith alg.hash ar' tl'))
    (hw_i : EqWidth w (combinedChildrenWith alg.hash ar_i tl_i))
    (hclen : (combinedChildrenWith alg.hash ar' tl').length
      = (combinedChildrenWith alg.hash ar_i tl_i).length)
    (hcommit : bindingRoot alg ar_i tl_i = alg.root)
    (haccept : Verifies alg ar' tl') :
    ar'.map (memberDigestWith alg.hash) = ar_i.map (memberDigestWith alg.hash)
      ∨ NodeHashCollisionFor alg.hash := by
  -- Both presented and committed structures fold (under Hᵢ) to the same root.
  have hroot : combinedRootWith alg.hash ar' tl' = combinedRootWith alg.hash ar_i tl_i := by
    simp only [bindingRoot] at hcommit
    simpa only [Verifies, bindingRoot, hcommit] using haccept
  rcases combinedChildrenWith_bound alg.hash hw' hw_i hclen
      (combinedChildrenWith_len_ge alg.hash hmulti')
      (combinedChildrenWith_len_ge alg.hash hmulti_i) hroot with hch | hcol
  · -- Equal child lists with equal member-prefix length: the member-byte
    -- prefixes coincide.
    left
    have hplen : (ar'.map (memberDigestWith alg.hash)).length
        = (ar_i.map (memberDigestWith alg.hash)).length := by
      simp only [List.length_map]; exact hlen
    simpa only [combinedChildrenWith] using List.append_inj_left hch hplen
  · exact Or.inr hcol

/-- **Singleton (promoted) binding-root soundness.** The one-member regime the
    multi-member `binding_root_sound` excludes (`ar.length ≥ 2`), closing the
    coverage gap the shipped API (`promoted_binding_root_verifies`) exercises. A
    single member root under a trivial activation promotes: `BRᵢ` *is* that member
    digest (`combinedRootWith_singleton`), with no node hash. So if algorithm `i`
    committed `[e_i]` (trivial `tl_i`) under `BRᵢ`, and a presented `[e']` (trivial
    `tl'`) verifies, the presented member digest equals the committed one —
    `memberDigestWith alg.hash e' = memberDigestWith alg.hash e_i` —
    **unconditionally**: promotion carries no hash, so no collision lever is
    needed (the conclusion has no `NodeHashCollisionFor` disjunct). -/
theorem binding_root_singleton_sound (alg : Algorithm)
    (e_i e' : AlgId × List UInt8) (tl_i tl' : Timeline)
    (htriv_i : timelineTrivial tl_i = true) (htriv' : timelineTrivial tl' = true)
    (hcommit : bindingRoot alg [e_i] tl_i = alg.root)
    (haccept : Verifies alg [e'] tl') :
    memberDigestWith alg.hash e' = memberDigestWith alg.hash e_i := by
  -- Both binding roots promote to their lone member digest.
  have hc : memberDigestWith alg.hash e_i = alg.root := by
    simpa only [bindingRoot, combinedRootWith_singleton alg.hash e_i tl_i htriv_i] using hcommit
  have ha : memberDigestWith alg.hash e' = alg.root := by
    simpa only [Verifies, bindingRoot, combinedRootWith_singleton alg.hash e' tl' htriv']
      using haccept
  rw [ha, hc]

/-- **Cross-algorithm consistency (`BRᵢ ≘ BRⱼ`).** If algorithms `i` and `j`
    genuinely committed structures under their own (independent) hashes, both in
    the multi-member regime over the presented active-set length, and a *single*
    presented `(ar', tl')` verifies against **both** binding roots, then the
    member-root child digests each committed agree with the presented ones — the
    algorithms agree on the same member roots — unless one of the two independent
    hashes collides. Each hash is applied only to its own children, so `i`'s
    guarantee never borrows `j`'s security. -/
theorem binding_proof_consistent {wi wj : Nat} (alg_i alg_j : Algorithm)
    (ar_i ar_j ar' : List (AlgId × List UInt8)) (tl_i tl_j tl' : Timeline)
    (hmulti_i : ar_i.length ≥ 2) (hmulti_j : ar_j.length ≥ 2) (hmulti' : ar'.length ≥ 2)
    (hlen_i : ar'.length = ar_i.length) (hlen_j : ar'.length = ar_j.length)
    (hwi' : EqWidth wi (combinedChildrenWith alg_i.hash ar' tl'))
    (hwi_i : EqWidth wi (combinedChildrenWith alg_i.hash ar_i tl_i))
    (hcleni : (combinedChildrenWith alg_i.hash ar' tl').length
      = (combinedChildrenWith alg_i.hash ar_i tl_i).length)
    (hwj' : EqWidth wj (combinedChildrenWith alg_j.hash ar' tl'))
    (hwj_j : EqWidth wj (combinedChildrenWith alg_j.hash ar_j tl_j))
    (hclenj : (combinedChildrenWith alg_j.hash ar' tl').length
      = (combinedChildrenWith alg_j.hash ar_j tl_j).length)
    (hcommit_i : bindingRoot alg_i ar_i tl_i = alg_i.root)
    (hcommit_j : bindingRoot alg_j ar_j tl_j = alg_j.root)
    (haccept_i : Verifies alg_i ar' tl')
    (haccept_j : Verifies alg_j ar' tl') :
    (ar'.map (memberDigestWith alg_i.hash) = ar_i.map (memberDigestWith alg_i.hash)
        ∧ ar'.map (memberDigestWith alg_j.hash) = ar_j.map (memberDigestWith alg_j.hash))
      ∨ NodeHashCollisionFor alg_i.hash ∨ NodeHashCollisionFor alg_j.hash := by
  rcases binding_root_sound alg_i ar_i ar' tl_i tl' hmulti_i hmulti' hlen_i
      hwi' hwi_i hcleni hcommit_i haccept_i with hi | hi
  · rcases binding_root_sound alg_j ar_j ar' tl_j tl' hmulti_j hmulti' hlen_j
        hwj' hwj_j hclenj hcommit_j haccept_j with hj | hj
    · exact Or.inl ⟨hi, hj⟩
    · exact Or.inr (Or.inr hj)
  · exact Or.inr (Or.inl hi)

/-- **Forgery rejection.** If the two algorithms genuinely committed *different*
    member-root child lists (under the presented structure), then no presented
    `(ar', tl')` can verify against **both** binding roots simultaneously, unless
    one of the independent hashes collides. The contrapositive of
    `binding_proof_consistent`: an inconsistent (forged) binding root is rejected
    by the cross-algorithm check, modulo collision. -/
theorem binding_proof_forgery_rejected {wi wj : Nat} (alg_i alg_j : Algorithm)
    (ar_i ar_j ar' : List (AlgId × List UInt8)) (tl_i tl_j tl' : Timeline)
    (hmulti_i : ar_i.length ≥ 2) (hmulti_j : ar_j.length ≥ 2) (hmulti' : ar'.length ≥ 2)
    (hlen_i : ar'.length = ar_i.length) (hlen_j : ar'.length = ar_j.length)
    (hwi' : EqWidth wi (combinedChildrenWith alg_i.hash ar' tl'))
    (hwi_i : EqWidth wi (combinedChildrenWith alg_i.hash ar_i tl_i))
    (hcleni : (combinedChildrenWith alg_i.hash ar' tl').length
      = (combinedChildrenWith alg_i.hash ar_i tl_i).length)
    (hwj' : EqWidth wj (combinedChildrenWith alg_j.hash ar' tl'))
    (hwj_j : EqWidth wj (combinedChildrenWith alg_j.hash ar_j tl_j))
    (hclenj : (combinedChildrenWith alg_j.hash ar' tl').length
      = (combinedChildrenWith alg_j.hash ar_j tl_j).length)
    (hcommit_i : bindingRoot alg_i ar_i tl_i = alg_i.root)
    (hcommit_j : bindingRoot alg_j ar_j tl_j = alg_j.root)
    (hdiff : ¬ (ar'.map (memberDigestWith alg_i.hash) = ar_i.map (memberDigestWith alg_i.hash)
        ∧ ar'.map (memberDigestWith alg_j.hash) = ar_j.map (memberDigestWith alg_j.hash)))
    (hno_coll_i : ¬ NodeHashCollisionFor alg_i.hash)
    (hno_coll_j : ¬ NodeHashCollisionFor alg_j.hash) :
    ¬ (Verifies alg_i ar' tl' ∧ Verifies alg_j ar' tl') := by
  rintro ⟨haccept_i, haccept_j⟩
  rcases binding_proof_consistent alg_i alg_j ar_i ar_j ar' tl_i tl_j tl'
      hmulti_i hmulti_j hmulti' hlen_i hlen_j hwi' hwi_i hcleni hwj' hwj_j hclenj
      hcommit_i hcommit_j haccept_i haccept_j with hagree | hcoll
  · exact hdiff hagree
  · rcases hcoll with hci | hcj
    · exact hno_coll_i hci
    · exact hno_coll_j hcj

end BindingProof
