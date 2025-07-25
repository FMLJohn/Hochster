import Mathlib.Data.Real.Basic

import Hochster.Section3

open CommRing Subring TopologicalSpace

structure CommRing.mulValuation (R : Type*) [CommRing R]
    extends MonoidWithZeroHom R ℝ where
  exists_of_ne_zero (r : R) : r ≠ 0 → ∃ n : ℤ, toFun r = 2 ^ n
  toFun_add_le_max (r s : R) : toFun (r + s) ≤ max (toFun r) (toFun s)

namespace CommRing.mulValuation

lemma toFun_pos_of_ne_zero {R : Type*} [CommRing R] (v : mulValuation R) {r : R} (hr : r ≠ 0) :
    0 < v.toFun r := by
  obtain ⟨n, hrn⟩ := v.exists_of_ne_zero r hr
  exact hrn ▸ zpow_pos zero_lt_two n

lemma toFun_ne_zero_of_ne_zero {R : Type*} [CommRing R] (v : mulValuation R) {r : R} (hr : r ≠ 0) :
    v.toFun r ≠ 0 :=
  (ne_of_lt <| toFun_pos_of_ne_zero v hr).symm

lemma toFun_div (F : Type*) [Field F] (v : mulValuation F) (r s : F) :
    v.toFun (r / s) = v.toFun r / v.toFun s := by
  by_cases hs : s = 0
  · exact hs ▸ v.map_zero' ▸ (div_zero r).symm ▸ (div_zero (v.toFun r)).symm ▸ v.map_zero'
  · simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe, map_div₀]

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

variable {X : Type*} [TopologicalSpace X]
variable {i : X → Type*} [(x : X) → Field (i x)] {A : Subring (Π x : X, i x)}

/--
The concept of an "index" of a spring mentioned on Page 47 of Hochster's paper.
-/
structure index (hXA : SpringLike' X A) where
  v : Π p : σ(X), mulValuation (i p.z.1)
  forall_le_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → (v p).toFun (a p.z.1) ≤ 1
  forall_iff_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → ((v p).toFun (a p.z.1) = 1 ↔ a p.z.2 ≠ 0)
  forall_exists_le : ∀ a ∈ A, ∃ r > (0 : ℝ), ∀ p : σ(X), a p.z.1 ≠ 0 → r ≤ (v p).toFun (a p.z.1)

/--
Given some `v : Π p : σ(X), mulValuation (i p.z.1)`, the property that it can be an index.
-/
class isIndex (hXA : SpringLike' X A)
    (v : Π p : σ(X), mulValuation (i p.z.1)) where
  forall_le_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → (v p).toFun (a p.z.1) ≤ 1
  forall_iff_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → ((v p).toFun (a p.z.1) = 1 ↔ a p.z.2 ≠ 0)
  forall_exists_le : ∀ a ∈ A, ∃ r > (0 : ℝ), ∀ p : σ(X), a p.z.1 ≠ 0 → r ≤ (v p).toFun (a p.z.1)

instance index.v_isIndex {hXA : SpringLike' X A} (index : hXA.index) :
    isIndex hXA index.v where
  forall_le_of_ne := index.forall_le_of_ne
  forall_iff_of_ne := index.forall_iff_of_ne
  forall_exists_le := index.forall_exists_le

def isIndex.toIndex {hXA : SpringLike' X A} {v : Π p : σ(X), mulValuation (i p.z.1)}
    (hv : hXA.isIndex v) : index hXA where
  v := v
  forall_le_of_ne := hv.forall_le_of_ne
  forall_iff_of_ne := hv.forall_iff_of_ne
  forall_exists_le := hv.forall_exists_le

end SpringLike'

lemma Pi.div_mul_cancel_of_forall_imp {ι : Type*} {G : ι → Type*} [(i : ι) → GroupWithZero (G i)]
    {f g : (i : ι) → G i} (hfg : ∀ i : ι, g i = 0 → f i = 0) : f / g * g = f := by
  ext i; by_cases hgi : g i = 0
  · exact hfg i hgi ▸ Pi.mul_apply _ g i ▸ hgi.symm ▸ mul_zero ((f / g) i)
  · exact Pi.mul_apply _ g i ▸ Pi.div_apply f g i ▸ div_mul_cancel_of_imp (hfg i)

namespace SpringLike'

variable {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
variable {A : Subring (Π x : X, i x)} {hXA : SpringLike' X A}

lemma index.toFun_mul_apply (index : hXA.index) (p : σ(X)) (a b : Π x : X, i x) :
    (index.v p).toFun ((a * b) p.z.1) =
      (index.v p).toFun (a p.z.1) * (index.v p).toFun (b p.z.1) :=
  Pi.mul_apply a b p.z.1 ▸ (index.v p).map_mul' ..

lemma index.toFun_zpow_apply (index : hXA.index) (p : σ(X)) (a : Π x : X, i x) (n : ℤ) :
    (index.v p).toFun ((a ^ n) p.z.1) = (index.v p).toFun (a p.z.1) ^ n :=
  Pi.pow_apply a n p.z.1 ▸ map_zpow₀ (index.v p).1 (a p.z.1) n

lemma index.toFun_div_apply (index : hXA.index) (p : σ(X)) (a b : Π x : X, i x) :
    (index.v p).toFun ((a / b) p.z.1) =
      (index.v p).toFun (a p.z.1) / (index.v p).toFun (b p.z.1) :=
  Pi.div_apply a b p.z.1 ▸ mulValuation.toFun_div (i p.z.1) (index.v p) (a p.z.1) (b p.z.1)

lemma index.toFun_div_apply_mul_toFun_apply_of_forall_imp (index : hXA.index)
    (p : σ(X)) {a b : Π x : X, i x} (hab : ∀ x : X, b x = 0 → a x = 0) :
    (index.v p).toFun ((a / b) p.z.1) * (index.v p).toFun (b p.z.1) =
      (index.v p).toFun (a p.z.1) :=
  index.toFun_mul_apply p .. ▸ Pi.mul_apply _ b p.z.1 ▸
    congr_fun (Pi.div_mul_cancel_of_forall_imp hab) p.z.1 ▸ rfl

lemma index.toFun_apply_le_v_extension {index : hXA.index}
    {a b : Π x : X, i x} (hab : ∀ x : X, b x = 0 → a x = 0) {p : σ(X)} (hap : a p.z.1 ≠ 0)
    {hXAab : SpringLike' X (Subring.closure (A ∪ {a / b}))} (hindex : isIndex hXAab index.v) :
    (index.v p).toFun (a p.z.1) ≤ (index.v p).toFun (b p.z.1) := by
  refine Pi.div_mul_cancel_of_forall_imp hab ▸ toFun_mul_apply index p _ b ▸
    (mul_le_iff_le_one_left ?_).2 ?_
  · exact mulValuation.toFun_pos_of_ne_zero _ fun hbp => hap (hab p.z.1 hbp)
  · refine hindex.toIndex.forall_le_of_ne p (a / b) ?_ (fun habp => ?_)
    · exact mem_closure_of_mem <| Set.mem_union_right _ rfl
    · exact Or.elim (div_eq_zero_iff.mp habp) hap (fun hbp => hap (hab p.z.1 hbp))

lemma index.ne_zero_of_v_extension_of_toFun_apply_eq {index : hXA.index}
    {a b : Π x : X, i x} (hab : ∀ x : X, b x = 0 → a x = 0) {p : σ(X)} (hap : a p.z.1 ≠ 0)
    {hXAab : SpringLike' X (Subring.closure (A ∪ {a / b}))} (hindex : isIndex hXAab index.v)
    (habp : (index.v p).toFun (a p.z.1) = (index.v p).toFun (b p.z.1)) :
    a p.z.2 ≠ 0 := by
  intro h
  have h1 : (a / b) p.z.2 = 0 := Pi.div_apply a b p.z.2 ▸ h ▸ zero_div (b p.z.2)
  have h2 : (a / b) p.z.1 ≠ 0 := fun h => hap <| hab p.z.1 <|
    (or_iff_not_imp_left.1 <| div_eq_zero_iff.1 <| Pi.div_apply a b p.z.1 ▸ h) hap
  have h3 : (hindex.toIndex.v p).toFun ((a / b) p.z.1) = 1 ↔ (a / b) p.z.2 ≠ 0 :=
    (hindex.toIndex.forall_iff_of_ne p (a / b) (mem_closure_of_mem <| Set.mem_union_right _ rfl) h2)
  have h4 : (hindex.toIndex.v p).toFun ((a / b) p.z.1) = 1 := hindex.toIndex.toFun_div_apply p a b
    ▸ (div_eq_one_iff_eq (habp ▸ (index.v p).toFun_ne_zero_of_ne_zero hap)).2 habp
  exact h3.1 h4 h1

end SpringLike'
