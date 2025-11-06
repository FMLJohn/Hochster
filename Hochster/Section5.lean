import Mathlib.Algebra.Ring.Hom.Defs

import Hochster.Section4

open Field Subring

/--
Note that this is different from the definition of a simple spring in the paper.
It is actually stronger!
-/
structure SpringLike'.isSimple {X : Type*}
    [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} (hA : SpringLike' A) where
  F : Type*
  field : Field F
  h (x : X) : i x →+* F
  forall_injective (x : X) : Function.Injective (h x)
  forall_finite : ∀ a ∈ A, { h x (a x) | x : X }.Finite

namespace SpringLike'.isIndex

def indExtForVSuccIsSimpleOfIsSimple {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} {hAv : hA.isIndex v}
    {n : ℕ} (h : (hAv.indExtForV n).isSimple) :
    (hAv.indExtForV (n + 1)).isSimple where
  F := h.F
  field := h.field
  h := h.h
  forall_injective := h.forall_injective
  forall_finite := fun a ha => by
    refine closure_induction ?_ ?_ ?_ ?_ ?_ ?_ ha
    · intro a ha
      refine Or.elim ha (fun ha => h.forall_finite a ha) ?_
      · intro ⟨b, c, habc, hb, hc, hcb, hAacn, hAacnv⟩
        refine habc ▸ (@(h.forall_finite b hb).div _ h.field.toDiv _ _
          (h.forall_finite c hc)).subset ?_
        · intro f ⟨x, hbcfx⟩
          refine ⟨h.h x (b x), ⟨x, rfl⟩, h.h x (c x), ⟨x, rfl⟩, ?_⟩
          sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry

def iSupExtForVIsSimpleOfIsSimple {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (h : hA.isSimple) (hAv : hA.isIndex v) :
    hAv.iSupExtForV.isSimple where
  F := h.F
  field := h.field
  h := sorry
  forall_injective := sorry
  forall_finite := sorry

end SpringLike'.isIndex
