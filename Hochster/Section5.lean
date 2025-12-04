import Mathlib.RingTheory.FreeCommRing

import Hochster.Section4

open Field Finset FreeCommRing Function RingHom Submodule Subring

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

lemma Subring.map_apply_eq_zero_of_pi_of_eq_of_eq_of_mem_span_of_eq
    {X : Type*} {x : X} {i : X → Type*} [(x : X) → CommRing (i x)]
    {A : Subring (Π x : X, i x)} {a b c : A} {R : Type*} [Ring R]
    {h : (x : X) → i x →+* R} (hahx : h x (a.1 x) = 0) (hbhx : h x (b.1 x) = 0)
    {m : FreeCommRing (Fin 2)} (hm : m ∈ Ideal.span { FreeCommRing.of 0, FreeCommRing.of 1 })
    (habcm : (lift fun i => if i = 0 then a else b) m = c) : h x (c.1 x) = 0 := by
  refine habcm ▸ span_induction (fun m hm => ?_) (h x).map_zero (fun m n _ _ hm hn => ?_)
    (fun m n hn habhnx => ?_) hm
  · exact hm.elim (fun hm => hm ▸ lift_of (fun i => if i = 0 then a else b) 0 ▸ hahx)
      (fun hm => hm ▸ lift_of (fun i => if i = 0 then a else b) 1 ▸ hbhx)
  · exact RingHom.map_add _ m n ▸ A.coe_add .. ▸ Pi.add_apply (M := i) .. ▸ (h x).map_add .. ▸
      hm.symm ▸ hn.symm ▸ add_zero 0
  · exact smul_eq_mul m n ▸ RingHom.map_mul _ m n ▸ A.coe_mul .. ▸ Pi.mul_apply (M := i) .. ▸
      (h x).map_mul .. ▸ habhnx.symm ▸ mul_zero _

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
    {A : Subring (Π x : X, i x)} (a b : A) {R : Type*} [Ring R] (h : (x : X) → i x →+* R) :=
  let s1 := { h x (a.1 x) | x : X }
  let s2 := { h x (b.1 x) | x : X }
  let S1 := { s : Set X | ∃ r ∈ s1, s = { x : X | h x (a.1 x) = r } }
  let S2 := { s : Set X | ∃ r ∈ s2, s = { x : X | h x (b.1 x) = r } }
  { s : Set X | s.Nonempty ∧ (∃ A ∈ S1, ∃ B ∈ S2, s = A ∩ B) ∧
    (∀ x ∈ s, h x (a.1 x) ≠ 0 ∨ h x (b.1 x) ≠ 0) }

namespace NonVanishingConstSetsFromInter

lemma sUnion_eq {X : Type*} {i : X → Type*} [(x : X) → Ring (i x)]
    {A : Subring (Π x : X, i x)} (a b : A) {R : Type*} [Ring R] (h : (x : X) → i x →+* R) :
    ⋃₀ (NonVanishingConstSetsFromInter a b h) = { x : X | h x (a.1 x) ≠ 0 ∨ h x (b.1 x) ≠ 0 } := by
  ext x
  refine ⟨fun ⟨s, ⟨_, _, habhsX⟩, hsx⟩ => habhsX x hsx, fun habhx =>
    ⟨{ y | h y (a.1 y) = h x (a.1 x) } ∩ { y | h y (b.1 y) = h x (b.1 x) },
      ⟨⟨x, rfl, rfl⟩, ?_, fun y ⟨hahy, hbhy⟩ => habhx.elim (fun hahx => ?_) (fun hbhx => ?_)⟩,
        rfl, rfl⟩⟩
  · exact ⟨{ y | h y (a.1 y) = h x (a.1 x) }, ⟨h x (a.1 x), ⟨x, rfl⟩, rfl⟩,
      { y | h y (b.1 y) = h x (b.1 x) }, ⟨h x (b.1 x), ⟨x, rfl⟩, rfl⟩, rfl⟩
  · exact Or.intro_left _ (hahy ▸ hahx)
  · exact Or.intro_right _ (hbhy ▸ hbhx)

lemma map_apply_eq_map_apply_of_mem_of_mem_of_apply_eq
    {X : Type*} {x y : X} {i : X → Type*} [(x : X) → CommRing (i x)]
    {A : Subring (Π x : X, i x)} {a b c : A} {R : Type*} [Ring R] {h : (x : X) → i x →+* R}
    {s : Set X} (habhs : s ∈ NonVanishingConstSetsFromInter a b h) (hsx : x ∈ s) (hsy : y ∈ s)
    {m : FreeCommRing (Fin 2)} (habcm : (lift fun i => if i = 0 then a else b) m = c) :
    h x (c.1 x) = h y (c.1 y) := by
  obtain ⟨_, ⟨t1, ⟨r1, ⟨x1, hahrx1⟩, hahrt1⟩, t2, ⟨r2, ⟨x2, hbhrx2⟩, hbhrt2⟩, hst12⟩, _⟩ := habhs
  refine A.map_apply_eq_map_apply_of_pi_of_eq_of_eq ?_ ?_ habcm
  · exact (hahrt1 ▸ (hst12 ▸ hsy).1) ▸ (hahrt1 ▸ (hst12 ▸ hsx).1 : x ∈ { x | h x (a.1 x) = r1 })
  · exact (hbhrt2 ▸ (hst12 ▸ hsy).2) ▸ (hbhrt2 ▸ (hst12 ▸ hsx).2 : x ∈ { x | h x (b.1 x) = r2 })

lemma map_apply_ne_zero_of_forall_mem_of_forall_ne_zero_of_apply_eq
    {X : Type*} {x : X} {i : X → Type*} [(x : X) → CommRing (i x)]
    {A : Subring (Π x : X, i x)} {a b c : A} {R : Type*} [Ring R]
    {h : (x : X) → i x →+* R} (habhx : h x (a.1 x) ≠ 0 ∨ h x (b.1 x) ≠ 0)
    {f : (s : Set X) → s ∈ NonVanishingConstSetsFromInter a b h → X}
    (habfh : ∀ (s : Set X) (hs : s ∈ NonVanishingConstSetsFromInter a b h), f s hs ∈ s)
    (habcfh : ∀ (s : Set X) (hs : s ∈ NonVanishingConstSetsFromInter a b h),
      h (f s hs) (c.1 (f s hs)) ≠ 0)
    {m : FreeCommRing (Fin 2)} (habcm : (lift fun i => if i = 0 then a else b) m = c) :
    h x (c.1 x) ≠ 0 := by
  obtain ⟨s, hs, hsx⟩ := sUnion_eq a b h ▸
    (Set.mem_setOf.2 habhx : x ∈ { x : X | h x (a.1 x) ≠ 0 ∨ h x (b.1 x) ≠ 0 })
  exact map_apply_eq_map_apply_of_mem_of_mem_of_apply_eq hs hsx (habfh s hs) habcm ▸ habcfh s hs

end NonVanishingConstSetsFromInter

open NonVanishingConstSetsFromInter

namespace SpringLike'

lemma finite_nonVanishingConstSetsFromInter_of_isSimple
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} (a b : A) {hA : SpringLike' A} (h : hA.isSimple) :
    (NonVanishingConstSetsFromInter a b h.h).Finite := by
  refine Set.Finite.subset
    (s := { s | ∃ A ∈ { s | ∃ r ∈ { f | ∃ x, h.h x (a.1 x) = f }, s = { x | h.h x (a.1 x) = r } },
      ∃ B ∈ { s | ∃ r ∈ { f | ∃ x, h.h x (b.1 x) = f }, s = { x | h.h x (b.1 x) = r } },
        s = A ∩ B }) ?_ fun s hs => hs.2.1
  · refine Set.Finite.subset
      (s := ({ s | ∃ r ∈ { f | ∃ x, h.h x (a.1 x) = f }, s = { x | h.h x (a.1 x) = r } } ×ˢ
        { s | ∃ r ∈ { f | ∃ x, h.h x (b.1 x) = f }, s = { x | h.h x (b.1 x) = r } }).image
          fun (A, B) => A ∩ B) ?_ fun s ⟨A, hA, B, hB, hABs⟩ => ⟨(A, B), ⟨hA, hB⟩, hABs.symm⟩
    · refine (Set.Finite.prod ?_ ?_).image _
      · exact ((h.forall_finite a a.2).image _).subset fun s ⟨r, hr, hs⟩ => ⟨r, hr, hs.symm⟩
      · exact ((h.forall_finite b b.2).image _).subset fun s ⟨r, hr, hs⟩ => ⟨r, hr, hs.symm⟩

lemma exists_mem_span_and_forall_map_apply_eq_zero_iff_and_of_isSimple
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} (a b : A) {hA : SpringLike' A} (h : hA.isSimple) :
    ∃ c : A, c ∈ Ideal.span {a, b} ∧ ∀ x : X, h.h x (c.1 x) = 0 ↔
      (h.h x (a.1 x) = 0 ∧ h.h x (b.1 x) = 0) := by
  by_cases hX : Nonempty X
  · choose f habfh using
      fun (s : Set X) (habhs : s ∈ NonVanishingConstSetsFromInter a b h.h) => habhs.1
    have : ¬∃ x ∈ { x | ∃ (s : Set X) (habhs : s ∈ NonVanishingConstSetsFromInter a b h.h),
        f s habhs = x }, Ideal.span {of 0, of 1} ≤ (hA.springLike.matchingIdeal x).comap
          (lift fun i : Fin 2 => if i = 0 then a else b) := by
      refine not_exists.2 fun x ⟨⟨s, habhs, habfhx⟩, hAabx⟩ =>
        (habhs.2.2 (f s habhs) (habfh s habhs)).elim (fun hafhs => ?_) (fun hbfhs => ?_)
      · have : a.1 x = 0 :=
          ((lift_of _ 0 : (lift fun i => if i = 0 then a else b) (of 0) = a) ▸
            ((hA.springLike.mem_matchingIdeal_iff_eq_zero x
              <| (lift fun i => if i = 0 then a else b) (of 0)).1
                <| hAabx <| Ideal.subset_span <| Set.mem_insert (of 0) _) :
                  hA.springLike.h (if 0 = 0 then a else b) x = 0)
        exact hafhs <| habfhx ▸ this ▸ (h.h x).map_zero
      · have : b.1 x = 0 :=
          ((lift_of _ 1 : (lift fun i => if i = 0 then a else b) (of 1) = b) ▸
            ((hA.springLike.mem_matchingIdeal_iff_eq_zero x
              <| (lift fun i => if i = 0 then a else b) (of 1)).1
                <| hAabx <| Ideal.subset_span <| Set.mem_insert_of_mem (of 0) rfl) :
                  hA.springLike.h (if 1 = 0 then a else b) x = 0)
        exact hbfhs <| habfhx ▸ this ▸ (h.h x).map_zero
    have ⟨m, hm, habmfh⟩ := Set.not_subset.1 <|
      (not_iff_not.2 <| (Ideal.span _).subset_union_prime_finite
        ((hA.finite_nonVanishingConstSetsFromInter_of_isSimple a b h).dependent_image f)
          (Classical.choice hX) (Classical.choice hX)
            (fun x _ _ _ => (hA.springLike.matchingIdeal_isPrime x).comap
              (lift (α := Fin 2) fun i => if i = 0 then a else b))).2 this
    refine ⟨(lift fun i => if i = 0 then a else b) m, ?_, fun x => ⟨?_, fun ⟨hahx, hbhx⟩ => ?_⟩⟩
    · refine span_induction (fun m hm => ?_) ?_ (fun m n _ _ hm hn => ?_)
        (fun m n _ hn => ?_) hm
      · refine hm.elim (fun hm => ?_) (fun hm => ?_)
        · exact hm ▸ lift_of (fun i => if i = 0 then a else b) 0 ▸ subset_span (Set.mem_insert a _)
        · exact hm ▸ lift_of (fun i => if i = 0 then a else b) 1 ▸
            subset_span (Set.mem_insert_of_mem a rfl)
      · exact (lift fun i => if i = 0 then a else b).map_zero ▸ zero_mem _
      · exact RingHom.map_add _ m n ▸ add_mem hm hn
      · exact smul_eq_mul m n ▸ RingHom.map_mul _ m n ▸ (Ideal.span _).mul_mem_left _ hn
    · refine not_imp_not.1 fun habhx =>
        map_apply_ne_zero_of_forall_mem_of_forall_ne_zero_of_apply_eq (not_and_or.1 habhx) habfh
          (fun s habhs => ?_) rfl
      · exact (map_ne_zero_iff _ <| h.forall_injective <| f s habhs).2 fun habhms =>
          habmfh <| Set.mem_iUnion₂.2 ⟨(f s habhs), ⟨s, habhs, rfl⟩,
            (hA.springLike.mem_matchingIdeal_iff_eq_zero (f s habhs) _).2 habhms⟩
    · exact map_apply_eq_zero_of_pi_of_eq_of_eq_of_mem_span_of_eq hahx hbhx hm rfl
  · exact ⟨0, zero_mem _, fun x => (not_nonempty_iff_imp_false.1 hX x).elim⟩

lemma exists_mem_span_and_forall_apply_eq_zero_iff_and_of_isSimple
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} (a b : A) {hA : SpringLike' A} (h : hA.isSimple) :
    ∃ c : A, c ∈ Ideal.span {a, b} ∧ ∀ x : X, c.1 x = 0 ↔ (a.1 x = 0 ∧ b.1 x = 0) := by
  obtain ⟨c, habc, habch⟩ :=
    hA.exists_mem_span_and_forall_map_apply_eq_zero_iff_and_of_isSimple a b h
  exact ⟨c, habc, fun x => (map_eq_zero_iff (h.h x) (h.forall_injective x)).symm.trans <|
    (habch x).trans <| Iff.and (map_eq_zero_iff (h.h x) (h.forall_injective x))
      (map_eq_zero_iff (h.h x) (h.forall_injective x))⟩

open Classical in
lemma exists_mem_span_and_forall_apply_eq_zero_iff_forall_of_isSimple
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} {B : Set A} (hB : B.Finite) {hA : SpringLike' A}
    (h : hA.isSimple) :
    ∃ c : A, c ∈ Ideal.span B ∧ ∀ x : X, c.1 x = 0 ↔ ∀ b ∈ B, b.1 x = 0 := by
  suffices ∀ (n : ℕ) (B : Set A) (hB : B.Finite), hB.toFinset.card = n →
    ∃ c : A, c ∈ Ideal.span B ∧ ∀ x : X, c.1 x = 0 ↔ ∀ b ∈ B, b.1 x = 0 from
      this hB.toFinset.card B hB rfl
  · intro n
    induction n with
    | zero =>
        exact fun B hB hB0 => ⟨0, zero_mem (Ideal.span B), fun x => ⟨fun _ b hbB =>
          (Set.notMem_empty b <| (hB.toFinset_eq_empty.1 <| card_eq_zero.1 hB0) ▸ hbB).elim,
            fun _ => A.coe_zero ▸ Pi.zero_apply (M := i) x ▸ rfl⟩⟩
    | succ n hn =>
        intro B hB hBn
        by_cases hn1 : 1 ≤ n
        · obtain ⟨b, hBb⟩ := card_ne_zero.1 <| hBn ▸ n.zero_ne_add_one.symm
          have : (hB.diff (t := {b})).toFinset.card = n := by
            have : hB.toFinset \ {b} = (hB.diff (t := {b})).toFinset := by
              ext
              simp only [mem_sdiff, Set.Finite.mem_toFinset, mem_singleton, Set.mem_diff,
                Set.mem_singleton_iff]
            exact this ▸ n.add_sub_cancel 1 ▸ card_singleton b ▸ hBn ▸
              (card_sdiff_of_subset <| singleton_subset_iff.2 hBb)
          obtain ⟨d, hBbd, hBXbd⟩ := hn (B \ {b}) hB.diff this
          obtain ⟨c, hBbcd, hBXbcd⟩ :=
            hA.exists_mem_span_and_forall_apply_eq_zero_iff_and_of_isSimple b d h
          refine ⟨c, ?_, fun x => (hBXbcd x).trans ⟨fun ⟨hbx, hdx⟩ => fun e hBe => ?_,
            fun hBX => ⟨hBX b (hB.mem_toFinset.1 hBb), ?_⟩⟩⟩
          · have : {b, d} ⊆ (Ideal.span B : Set A) :=
              fun a ha => ha.elim (fun hab => hab ▸ subset_span (hB.mem_toFinset.1 hBb))
                (fun had => had ▸ span_mono B.diff_subset hBbd)
            exact span_le.2 this hBbcd
          · by_cases hbe : e = b
            · exact hbe ▸ hbx
            · exact (hBXbd x).1 hdx e (B.mem_diff_of_mem hBe hbe)
          · exact (hBXbd x).2 fun e hBbe => hBX e (B.diff_subset hBbe)
        · obtain ⟨b, hBb⟩ := card_eq_one.1 <| zero_add 1 ▸ (Nat.lt_one_iff.1 <| lt_of_not_ge hn1) ▸
            hBn
          exact (coe_singleton b ▸ hBb ▸ hB.coe_toFinset) ▸ ⟨b, subset_span (Set.mem_singleton b),
            fun x => ⟨fun hbx _ h => Set.eq_of_mem_singleton h ▸ hbx, fun hx => hx b rfl⟩⟩

lemma exists_mem_span_and_eq_biInter_of_isSimple {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {A : Subring (Π x : X, i x)}
    {B : Set A} (hB : B.Finite) {hA : SpringLike' A} (h : hA.isSimple) :
    ∃ c : A, c ∈ Ideal.span B ∧ { x : X | c.1 x = 0 } = ⋂ b ∈ B, { x : X | b.1 x = 0 } := by
  obtain ⟨c, hBc, hBXc⟩ := exists_mem_span_and_forall_apply_eq_zero_iff_forall_of_isSimple hB h
  refine ⟨c, hBc, ?_⟩
  · ext x
    simpa only [Set.mem_iInter] using hBXc x

/-- This corresponds to the second statement in Theorem 4 of the paper. -/
lemma springLike_spring_isAffine_of_isSimple_of_forall_imp
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (h1 : hA.isSimple)
    (h2 : ∀ a b : A, (∀ x : X, b.1 x = 0 → a.1 x = 0) → a ∈ (Ideal.span {b}).radical) :
    hA.springLike.spring.isAffine := by
  refine hA.springLike_spring_isAffine_iff_forall_mem_radical_of_subset.2 fun a B hB haBX => ?_
  · obtain ⟨c, hBc, hBXc⟩ := exists_mem_span_and_eq_biInter_of_isSimple hB h1
    exact (Ideal.radical_mono <| span_le.2 <| Set.singleton_subset_iff.2 hBc)
      (h2 a c fun x hcx => haBX <| hBXc ▸ Set.mem_setOf.2 hcx)

/-- This corresponds to the third statement in Theorem 4 of the paper. -/
lemma isIndex.iSupExtForV_springLike_spring_isAffine_of_isSimple
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (h : hA.isSimple) (hAv : hA.isIndex v) :
    hAv.iSupExtForV.springLike.spring.isAffine :=
  hAv.iSupExtForV.springLike_spring_isAffine_of_isSimple_of_forall_imp
    (hAv.iSupExtForVIsSimpleOfIsSimple h)
    (fun _ _ => hAv.mem_radical_span_singleton_of_forall_imp)

end SpringLike'
