import Mathlib.Data.Real.Basic

import Hochster.Section3

open CommRing TopologicalSpace

structure CommRing.mulValuation (R : Type*) [CommRing R]
    extends MonoidWithZeroHom R ℝ where
  exists_of_ne_zero (r : R) : r ≠ 0 → ∃ n : ℤ, toFun r = 2 ^ n
  toFun_add_le_max (r s : R) : toFun (r + s) ≤ max (toFun r) (toFun s)

namespace CommRing.mulValuation

lemma toFun_pos_of_ne_zero {R : Type*} [CommRing R] (v : mulValuation R) {r : R} (hr : r ≠ 0) :
    0 < v.toFun r := by
  obtain ⟨n, hrn⟩ := v.exists_of_ne_zero r hr
  exact hrn ▸ zpow_pos zero_lt_two n

lemma toFun_neg {R : Type*} [CommRing R] (v : mulValuation R) (r : R) :
    v.toFun (-r) = v.toFun r := by
  by_cases hr : r = 0
  · exact hr ▸ v.map_zero' ▸ (neg_zero (G := R)).symm ▸ v.map_zero'
  · have : (v.toFun (-r)) ^ 2 = (v.toFun r) ^ 2 :=
      pow_two (v.toFun (-r)) ▸ pow_two (v.toFun r) ▸ v.map_mul' .. ▸ v.map_mul' .. ▸
        (neg_mul_neg r r).symm ▸ rfl
    exact (or_iff_not_imp_right.1 <| eq_or_eq_neg_of_sq_eq_sq _ _ this)
      fun h => (lt_asymm <| h ▸ neg_neg_iff_pos.mpr <| toFun_pos_of_ne_zero v hr)
        (toFun_pos_of_ne_zero v <| neg_ne_zero.mpr hr)

lemma toFun_add_eq_max_of_ne {R : Type*} [CommRing R]
    (v : mulValuation R) {r s : R} (hrs : v.toFun r ≠ v.toFun s) :
    v.toFun (r + s) = max (v.toFun r) (v.toFun s) := by
  refine eq_of_le_of_ge (v.toFun_add_le_max r s) ?_
  · by_cases h : v.toFun r < v.toFun s
    · exact (max_eq_right_of_lt h).symm ▸ by_contradiction fun h1 => by
        have := zero_add s ▸ neg_add_cancel r ▸ add_assoc (-r) r s ▸ add_comm (r + s) (-r) ▸
          v.toFun_neg r ▸ v.toFun_add_le_max (r + s) (-r)
        exact (lt_self_iff_false (v.toFun s)).1 <| lt_of_le_of_lt this <| max_lt (lt_of_not_ge h1) h
    · refine (max_eq_left_of_lt <| lt_of_le_of_ne (le_of_not_gt h) hrs.symm).symm ▸ ?_
      · by_contra h1
        have := v.toFun_neg s ▸ add_zero r ▸ add_neg_cancel s ▸ add_assoc r s (-s) ▸
          v.toFun_add_le_max (r + s) (-s)
        exact (lt_self_iff_false (v.toFun r)).1 <| lt_of_le_of_lt this <|
          max_lt (lt_of_not_ge h1) (lt_of_le_of_ne (le_of_not_gt h) hrs.symm)

end CommRing.mulValuation

/--
The type of pairs `(x, y) : X × X` such that `y ∈ closure {x}`.
-/
structure memClosurePairs (X : Type*) [TopologicalSpace X] where
  z : X × X
  mem_closure : z.2 ∈ closure {z.1}

notation "σ("X")" => memClosurePairs X

namespace SpringLike'

/--
The concept of an "index" of a spring mentioned on Page 47 of Hochster's paper.
-/
structure index {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} (hXA : SpringLike' X A) where
  v : Π p : σ(X), mulValuation (i p.z.1)
  forall_le_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → (v p).toFun (a p.z.1) ≤ 1
  forall_iff_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → ((v p).toFun (a p.z.1) = 1 ↔ a p.z.2 ≠ 0)
  forall_exists_le : ∀ a ∈ A, ∃ r > (0 : ℝ), ∀ p : σ(X), a p.z.1 ≠ 0 → r ≤ (v p).toFun (a p.z.1)

/--
Given some `v : Π p : σ(X), mulValuation (i p.z.1)`, the property that it can be an index.
-/
class isIndex {X : Type*} [TopologicalSpace X] {i : X → Type*}
    [(x : X) → Field (i x)] {A : Subring (Π x : X, i x)} (hXA : SpringLike' X A)
    (v : Π p : σ(X), mulValuation (i p.z.1)) where
  forall_le_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → (v p).toFun (a p.z.1) ≤ 1
  forall_iff_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → ((v p).toFun (a p.z.1) = 1 ↔ a p.z.2 ≠ 0)
  forall_exists_le : ∀ a ∈ A, ∃ r > (0 : ℝ), ∀ p : σ(X), a p.z.1 ≠ 0 → r ≤ (v p).toFun (a p.z.1)

instance index.v_isIndex {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {A : Subring (Π x : X, i x)}
    {hXA : SpringLike' X A} (index : hXA.index) :
    isIndex hXA index.v where
  forall_le_of_ne := index.forall_le_of_ne
  forall_iff_of_ne := index.forall_iff_of_ne
  forall_exists_le := index.forall_exists_le

def isIndex.toIndex {X : Type*} [TopologicalSpace X] {i : X → Type*}
    [(x : X) → Field (i x)] {A : Subring (Π x : X, i x)} {hXA : SpringLike' X A}
    {v : Π p : σ(X), mulValuation (i p.z.1)} (hv : hXA.isIndex v) :
    index hXA where
  v := v
  forall_le_of_ne := hv.forall_le_of_ne
  forall_iff_of_ne := hv.forall_iff_of_ne
  forall_exists_le := hv.forall_exists_le

end SpringLike'
