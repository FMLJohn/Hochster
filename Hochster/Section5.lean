import Mathlib.RingTheory.FreeCommRing

import Hochster.Section4

open Field FreeCommRing Function RingHom Submodule Subring

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

attribute [instance] SpringLike'.isSimple.field

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

def indExtForVIsSimpleOfIsSimple {X : Type*}
    [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (h : hA.isSimple) (hAv : hA.isIndex v) (n : ℕ) :
    (hAv.indExtForV n).isSimple :=
  n.recAuxOn h fun _ hn => hAv.indExtForVSuccIsSimpleOfIsSimple hn

lemma indExtForVIsSimpleOfIsSimple_f {X : Type*}
    [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (h : hA.isSimple) (hAv : hA.isIndex v) (n : ℕ) :
    (hAv.indExtForVIsSimpleOfIsSimple h n).F = h.F := by
   induction n with
  | zero => rfl
  | succ n hn => exact hn

lemma indExtForVIsSimpleOfIsSimple_h {X : Type*}
    [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (h : hA.isSimple) (hAv : hA.isIndex v) (n : ℕ) :
    (hAv.indExtForVIsSimpleOfIsSimple h n).h ≍ h.h := by
  induction n with
  | zero => rfl
  | succ n hn => exact hn

lemma indExtForVIsSimpleOfIsSimple_h' {X : Type*}
    [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (h : hA.isSimple) (hAv : hA.isIndex v) (x : X) (n : ℕ) :
    ((hAv.indExtForVIsSimpleOfIsSimple h n).h x).toFun =
      (hAv.indExtForVIsSimpleOfIsSimple_f h n).symm.mp ∘ (h.h x).toFun := by
  induction n with
  | zero => rfl
  | succ n hn => exact hn

/-- This corresponds to the first statement in Theorem 4 of the paper. -/
def iSupExtForVIsSimpleOfIsSimple {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (h : hA.isSimple) (hAv : hA.isIndex v) :
    hAv.iSupExtForV.isSimple where
  F := h.F
  field := h.field
  h := h.h
  forall_injective := h.forall_injective
  forall_finite := fun a hAav => by
    obtain ⟨n, hAanv⟩ := (mem_iSupExtForV_iff v A a).1 hAav
    have : { h.h x (a x) | x : X } ⊆ (hAv.indExtForVIsSimpleOfIsSimple_f h n).mp ''
        { (indExtForVIsSimpleOfIsSimple h hAv n).h x (a x) | x : X } := by
      intro f ⟨x, hafx⟩
      refine ⟨(hAv.indExtForVIsSimpleOfIsSimple_f h n).symm.mp f, ⟨x, ?_⟩, ?_⟩
      · have := Function.comp_apply ▸ congr_fun (hAv.indExtForVIsSimpleOfIsSimple_h' h x n) (a x)
        exact hafx ▸ this
      · simp only [eq_mp_eq_cast, cast_cast, cast_eq]
    exact (((hAv.indExtForVIsSimpleOfIsSimple h n).forall_finite a hAanv).image
      (indExtForVIsSimpleOfIsSimple_f h hAv n).mp).subset this

end SpringLike'.isIndex

example {R : Type*} [CommRing R] (r s : R) :
    FreeCommRing (Fin 2) →+* R :=
  lift fun i => if i = 0 then r else s

lemma Subring.map_apply_eq_map_apply_of_pi_of_eq_of_eq {X : Type*} {x y : X}
    {i : X → Type*} [(x : X) → CommRing (i x)] {A : Subring (Π x : X, i x)}
    {a b c : A} {R : Type*} [Ring R] {h : (x : X) → i x →+* R}
    (hahxy : h x (a.1 x) = h y (a.1 y)) (hbhxy : h x (b.1 x) = h y (b.1 y))
    {m : FreeCommRing (Fin 2)} (habcm : (lift fun i => if i = 0 then a else b) m = c) :
    h x (c.1 x) = h y (c.1 y) := by
  refine habcm ▸ m.induction_on ?_ (fun m => ?_) (fun m n habhmxy habhnxy => ?_)
    (fun m n habhmxy habhnxy => ?_)
  · exact (lift fun i => if i = 0 then a else b).map_neg 1 ▸
      (lift fun i => if i = 0 then a else b).map_one ▸ A.coe_neg 1 ▸ A.coe_one ▸
      Pi.neg_apply (G := i) 1 x ▸ Pi.one_apply (M := i) x ▸ Pi.neg_apply (G := i) 1 y ▸
      Pi.one_apply (M := i) y ▸ (h x).map_neg 1 ▸ (h y).map_neg 1 ▸ (h x).map_one ▸
      (h y).map_one ▸ rfl
  · by_cases hm : m = 0
    · exact hm.symm ▸ lift_of (fun i => if i = 0 then a else b) 0 ▸ hahxy
    · simp only [lift_of, hm]
      exact hbhxy
  · exact RingHom.map_add .. ▸ (h x).map_add .. ▸ (h y).map_add .. ▸ habhmxy ▸ habhnxy ▸ rfl
  · exact RingHom.map_mul .. ▸ (h x).map_mul .. ▸ (h y).map_mul .. ▸ habhmxy ▸ habhnxy ▸ rfl

def NonVanishingConstSetsFromInter {X : Type*} {i : X → Type*} [(x : X) → Ring (i x)]
    {A : Subring (Π x : X, i x)} (a b : A) {F : Type*} [Ring F] (h : (x : X) → i x →+* F) :=
  let s1 := { h x (a.1 x) | x : X }
  let s2 := { h x (b.1 x) | x : X }
  let S1 := { s : Set X | ∃ f ∈ s1, s = { x : X | h x (a.1 x) = f } }
  let S2 := { s : Set X | ∃ f ∈ s2, s = { x : X | h x (a.1 x) = f } }
  { s : Set X | s.Nonempty ∧ (∃ A ∈ S1, ∃ B ∈ S2, s = A ∩ B) ∧
    (∀ x ∈ s, ¬a.1 x = 0 ∨ ¬b.1 x = 0) }
