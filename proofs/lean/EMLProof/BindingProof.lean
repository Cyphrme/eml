import EMLProof.Foundations
import EMLProof.NEML

/-!
# Binding-proof soundness (PMT, over `Foundations`)

The **binding proof** is the cross-algorithm peer of inclusion / consistency /
leaf / snapshot proofs (`pmt/src/binding_proof.rs`). It proves that a set of
per-algorithm *binding roots* are mutually consistent: that every algorithm has
committed, under its **own** hash, to the *same* logical structure — the same
member-root tuple `ar` and the same committed epoch timeline `tl`.

## The per-algorithm binding root (no security mixing)

Each algorithm `i` carries its own hash `Hᵢ` and its own binding root

```text
BRᵢ = Hᵢ( metaPreimage ar tl )
```

where `metaPreimage ar tl` is the canonical preimage of the shared member roots
and committed timeline (`NEML.metaPreimage`, mirroring `combined_root_preimage`
in `pmt/src/proof.rs`). Critically, `Hᵢ` is applied **only** to the shared opaque
preimage; no other algorithm's binding root ever enters `Hᵢ`. This is design
decision **D9** — *no security mixing* — modelled here by giving each algorithm
an *independent* hash function `Hᵢ` as a parameter, never the same hash applied
across algorithms' secrets. Collision resistance of `BRᵢ` is the collision
resistance of `Hᵢ` alone, captured below as the discharged hypothesis
`¬ HashCollisionFor Hᵢ`.

## Trust base

This module adds **no axiom**. It is parameterized by the per-algorithm hashes
`Hᵢ` (ordinary function parameters) and reuses `NEML.metaPreimage_injective` —
itself a hash-agnostic structural fact about the canonical byte encoding. Every
theorem here reports a `#print axioms` subset of the four `Foundations` axioms
(`Digest`, `Digest.nonempty`, `H`, `digestToBytes`) plus the Lean built-ins.

## What is proven

* `binding_root_sound` — *per-algorithm soundness*: if a presented structure
  `(ar', tl')` produces algorithm `i`'s trusted binding root under `Hᵢ`, then it
  equals what `i` genuinely committed (`(ar', tl') = (arᵢ, tlᵢ)`) unless `Hᵢ`
  collides. The forgery direction: a presented structure inconsistent with what
  `i` committed cannot reproduce `BRᵢ` (modulo collision), so it is rejected.
* `binding_proof_consistent` — *cross-algorithm consistency*: if a single
  presented `(ar', tl')` verifies for **both** algorithms `i` and `j`, then the
  structures they genuinely committed coincide (`(arᵢ, tlᵢ) = (arⱼ, tlⱼ)`) — the
  algorithms agree, `BRᵢ ≘ BRⱼ` — unless one of the two independent hashes
  collides. No algorithm's hash is ever applied to another's binding root, so a
  break of `Hⱼ` cannot manufacture agreement under `Hᵢ`.
* `binding_proof_forgery_rejected` — *forgery rejection*: if the two algorithms
  genuinely committed to **different** structures, then no presented `(ar', tl')`
  can verify against both binding roots at once, unless a hash collides.
-/

namespace BindingProof

open NEML

/-- A collision in a *specific* algorithm's hash `Hᵢ`. This is the per-algorithm
    analogue of `NEML.HashCollision` (which is fixed to the abstract `Foundations`
    hash `H`). Each algorithm's binding-root security rests on the
    non-collision of its **own** hash alone — the formal statement of D9's
    no-security-mixing guarantee. -/
def HashCollisionFor (Hi : List UInt8 → Digest) : Prop :=
  ∃ a b : List UInt8, a ≠ b ∧ Hi a = Hi b

/-- One algorithm's contribution to a binding proof: its own hash `hash` (`Hᵢ`)
    and the binding root `root` (`BRᵢ`) it is trusted to have published. The
    structure it actually committed (`ar`, `tl`) is what soundness recovers. -/
structure Algorithm where
  /-- That algorithm's own hash `Hᵢ`. Applied only to the shared opaque
      preimage; never to another algorithm's binding root (D9). -/
  hash : List UInt8 → Digest
  /-- The trusted binding root `BRᵢ` this algorithm published. -/
  root : Digest

/-- The binding root algorithm `i` obtains for a structure `(ar, tl)`: its own
    hash applied to the shared canonical preimage. Mirrors `BindingProof::verify`
    in `pmt/src/binding_proof.rs`, which recomputes `Hᵢ(preimage)` per algorithm. -/
noncomputable def bindingRoot (alg : Algorithm)
    (ar : List (AlgId × List UInt8)) (tl : Timeline) : Digest :=
  alg.hash (metaPreimage ar tl)

/-- The verifier's per-algorithm accept relation: the presented structure
    `(ar', tl')` hashes, under `alg`'s own hash, to `alg`'s trusted binding root.
    Mirrors the `constant_time_eq(Hᵢ(preimage), BRᵢ)` check in `verify`. -/
def Verifies (alg : Algorithm)
    (ar' : List (AlgId × List UInt8)) (tl' : Timeline) : Prop :=
  bindingRoot alg ar' tl' = alg.root

/-- **Per-algorithm binding-root soundness.** Let `(arᵢ, tlᵢ)` be the structure
    algorithm `i` genuinely committed under its binding root (`bindingRoot alg
    arᵢ tlᵢ = alg.root`). If a presented `(ar', tl')` verifies against the same
    binding root, then it *is* the committed structure — `(ar', tl') = (arᵢ,
    tlᵢ)` — unless `alg`'s own hash collides. The committed structure is
    *derived* from the canonical-encoding injectivity, never assumed. -/
theorem binding_root_sound (alg : Algorithm)
    (ar_i ar' : List (AlgId × List UInt8)) (tl_i tl' : Timeline)
    (hcommit : bindingRoot alg ar_i tl_i = alg.root)
    (haccept : Verifies alg ar' tl') :
    (ar' = ar_i ∧ tl' = tl_i) ∨ HashCollisionFor alg.hash := by
  -- Both presented and committed preimages hash (under Hᵢ) to the same root.
  have hroot : alg.hash (metaPreimage ar' tl') = alg.hash (metaPreimage ar_i tl_i) := by
    simp only [bindingRoot] at hcommit
    simpa only [Verifies, bindingRoot, hcommit] using haccept
  by_cases hpre : metaPreimage ar' tl' = metaPreimage ar_i tl_i
  · -- Equal preimages force equal structure by canonical-encoding injectivity.
    exact Or.inl (metaPreimage_injective hpre)
  · -- Distinct preimages with equal Hᵢ-images is a collision in Hᵢ.
    exact Or.inr ⟨metaPreimage ar' tl', metaPreimage ar_i tl_i, hpre, hroot⟩

/-- **Cross-algorithm consistency (`BRᵢ ≘ BRⱼ`).** Suppose algorithms `i` and `j`
    genuinely committed structures `(arᵢ, tlᵢ)` and `(arⱼ, tlⱼ)` under their own
    (independent) hashes, and a *single* presented structure `(ar', tl')`
    verifies against **both** binding roots. Then the two committed structures
    coincide — the algorithms agree on the same logical structure — unless one of
    the two independent hashes collides. Each algorithm's hash is applied only to
    the shared preimage, so the guarantee for `i` never borrows `j`'s security. -/
theorem binding_proof_consistent (alg_i alg_j : Algorithm)
    (ar_i ar_j ar' : List (AlgId × List UInt8)) (tl_i tl_j tl' : Timeline)
    (hcommit_i : bindingRoot alg_i ar_i tl_i = alg_i.root)
    (hcommit_j : bindingRoot alg_j ar_j tl_j = alg_j.root)
    (haccept_i : Verifies alg_i ar' tl')
    (haccept_j : Verifies alg_j ar' tl') :
    ((ar_i = ar_j) ∧ (tl_i = tl_j))
      ∨ HashCollisionFor alg_i.hash ∨ HashCollisionFor alg_j.hash := by
  -- Each algorithm's soundness pins the presented structure to its committed one.
  rcases binding_root_sound alg_i ar_i ar' tl_i tl' hcommit_i haccept_i with hi | hi
  · rcases binding_root_sound alg_j ar_j ar' tl_j tl' hcommit_j haccept_j with hj | hj
    · -- (ar', tl') = (arᵢ, tlᵢ) and = (arⱼ, tlⱼ): the committed structures agree.
      obtain ⟨har_i, htl_i⟩ := hi
      obtain ⟨har_j, htl_j⟩ := hj
      exact Or.inl ⟨har_i ▸ har_j, htl_i ▸ htl_j⟩
    · exact Or.inr (Or.inr hj)
  · exact Or.inr (Or.inl hi)

/-- **Forgery rejection.** If the two algorithms genuinely committed to
    *different* structures (`(arᵢ, tlᵢ) ≠ (arⱼ, tlⱼ)`), then no presented
    `(ar', tl')` can verify against **both** binding roots simultaneously, unless
    one of the independent hashes collides. The contrapositive of
    `binding_proof_consistent`: an inconsistent (forged) binding root is rejected
    by the cross-algorithm check, modulo collision. -/
theorem binding_proof_forgery_rejected (alg_i alg_j : Algorithm)
    (ar_i ar_j ar' : List (AlgId × List UInt8)) (tl_i tl_j tl' : Timeline)
    (hcommit_i : bindingRoot alg_i ar_i tl_i = alg_i.root)
    (hcommit_j : bindingRoot alg_j ar_j tl_j = alg_j.root)
    (hdiff : ¬ ((ar_i = ar_j) ∧ (tl_i = tl_j)))
    (hno_coll_i : ¬ HashCollisionFor alg_i.hash)
    (hno_coll_j : ¬ HashCollisionFor alg_j.hash) :
    ¬ (Verifies alg_i ar' tl' ∧ Verifies alg_j ar' tl') := by
  rintro ⟨haccept_i, haccept_j⟩
  rcases binding_proof_consistent alg_i alg_j ar_i ar_j ar' tl_i tl_j tl'
      hcommit_i hcommit_j haccept_i haccept_j with hagree | hcoll
  · exact hdiff hagree
  · rcases hcoll with hci | hcj
    · exact hno_coll_i hci
    · exact hno_coll_j hcj

end BindingProof
