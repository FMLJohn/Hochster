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
    letI := h.field
    refine closure_induction (fun a ha => ?_) ?_ ?_ (fun a b _ _ ha hb => ?_) (fun a _ ha => ?_)
      (fun a b _ _ ha hb => ?_) ha
    · refine Or.elim ha (fun ha => h.forall_finite a ha) ?_
      · intro ⟨b, c, habc, hb, hc, hcb, hAacn, hAacnv⟩
        exact habc ▸ ((h.forall_finite b hb).div (h.forall_finite c hc)).subset
          fun f ⟨x, hbcfx⟩ => ⟨h.h x (b x), ⟨x, rfl⟩, h.h x (c x), ⟨x, rfl⟩,
            hbcfx ▸ Pi.div_apply b c x ▸ (map_div₀ (h.h x) (b x) (c x)).symm⟩
    · have : { h.h x ((0 : (x : X) → i x) x) | x : X } ⊆ {0} :=
        fun f ⟨x, hfx⟩ => hfx ▸ (map_eq_zero (h.h x)).2 (Pi.zero_apply x) ▸ rfl
      exact (Set.finite_singleton 0).subset this
    · have : { h.h x ((1 : (x : X) → i x) x) | x : X } ⊆ {1} :=
        fun f ⟨x, hfx⟩ => hfx ▸ (h.h x).map_one ▸ rfl
      exact (Set.finite_singleton 1).subset this
    · exact (ha.add hb).subset fun f ⟨x, habfx⟩ =>
        ⟨h.h x (a x), ⟨x, rfl⟩, h.h x (b x), ⟨x, rfl⟩,
          (Pi.add_apply a b x ▸ habfx) ▸ ((h.h x).map_add (a x) (b x)).symm⟩
    · exact ha.neg.subset fun f ⟨x, hafx⟩ =>
        ⟨x, ((Pi.neg_apply a x ▸ hafx) ▸ (h.h x).map_neg (a x)) ▸ (neg_neg _).symm⟩
    · exact (ha.mul hb).subset fun f ⟨x, habfx⟩ =>
        ⟨h.h x (a x), ⟨x, rfl⟩, h.h x (b x), ⟨x, rfl⟩,
          (Pi.mul_apply a b x ▸ habfx) ▸ ((h.h x).map_mul (a x) (b x)).symm⟩

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
