import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic

import Mathlib

import Hochster.Section3

open CommRing Polynomial SpringLike' Subring TopologicalSpace Valuation

/--
The type of pairs `(x, y) : X × X` such that `y ∈ closure {x}`.
-/
structure MemClosurePairs (X : Type*) [TopologicalSpace X] where
  z : X × X
  mem_closure : z.2 ∈ closure {z.1}

notation "σ("X")" => MemClosurePairs X

lemma Pi.div_mul_cancel_of_forall_imp {ι : Type*} {G : ι → Type*} [(i : ι) → GroupWithZero (G i)]
    {f g : (i : ι) → G i} (hfg : ∀ i : ι, g i = 0 → f i = 0) : f / g * g = f := by
  ext i; by_cases hgi : g i = 0
  · exact hfg i hgi ▸ Pi.mul_apply _ g i ▸ hgi.symm ▸ mul_zero ((f / g) i)
  · exact Pi.mul_apply _ g i ▸ Pi.div_apply f g i ▸ div_mul_cancel_of_imp (hfg i)

namespace MemClosurePairs

lemma map_mul_apply_of_pi_valuation {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Ring (i x)] (v : Π p : σ(X), Valuation (i p.z.1) NNRat)
    (p : σ(X)) (a b : Π x : X, i x) :
    v p ((a * b) p.z.1) = v p (a p.z.1) * v p (b p.z.1) :=
  Pi.mul_apply a b p.z.1 ▸ (v p).map_mul' ..

lemma map_zpow_apply_of_pi_valuation {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] (v : Π p : σ(X), Valuation (i p.z.1) NNRat)
    (p : σ(X)) (a : Π x : X, i x) (n : ℤ) :
    v p ((a ^ n) p.z.1) = v p (a p.z.1) ^ n :=
  Pi.pow_apply a n p.z.1 ▸ map_zpow₀ (v p).1 (a p.z.1) n

lemma map_div_apply_of_pi_valuation {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] (v : Π p : σ(X), Valuation (i p.z.1) NNRat)
    (p : σ(X)) (a b : Π x : X, i x) :
    v p ((a / b) p.z.1) = v p (a p.z.1) / v p (b p.z.1) :=
  Pi.div_apply a b p.z.1 ▸ (v p).map_div (a p.z.1) (b p.z.1)

lemma map_div_apply_mul_map_apply_of_pi_valuation_of_forall_imp
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    (v : Π p : σ(X), Valuation (i p.z.1) NNRat) (p : σ(X)) {a b : Π x : X, i x}
    (hab : ∀ x : X, b x = 0 → a x = 0) :
    v p ((a / b) p.z.1) * v p (b p.z.1) = v p (a p.z.1) :=
  p.map_mul_apply_of_pi_valuation v (a / b) b ▸
    congr_fun (Pi.div_mul_cancel_of_forall_imp hab) p.z.1 ▸ rfl

end MemClosurePairs

/--
Given some `v : Π p : σ(X), mulValuation (i p.z.1)`, the property that it can be an index of the
spring.
-/
structure SpringLike'.isIndex {X : Type*} [TopologicalSpace X] {i : X → Type*}
    [(x : X) → Field (i x)] {A : Subring (Π x : X, i x)} (hA : SpringLike' A)
    (v : Π p : σ(X), Valuation (i p.z.1) NNRat) where
  forall_isRankOneDiscrete (p : σ(X)) : (v p).IsRankOneDiscrete
  forall_le_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → v p (a p.z.1) ≤ 1
  forall_iff_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → (v p (a p.z.1) = 1 ↔ a p.z.2 ≠ 0)
  forall_exists_le : ∀ a ∈ A, ∃ r > (0 : ℝ), ∀ p : σ(X), a p.z.1 ≠ 0 → r ≤ v p (a p.z.1)

namespace MemClosurePairs

lemma map_apply_le_of_pi_valuation_of_v_extension {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {a b : Π x : X, i x} (hab : ∀ x : X, b x = 0 → a x = 0)
    {p : σ(X)} (hap : a p.z.1 ≠ 0) {hAab : SpringLike' (Subring.closure (A ∪ {a / b}))}
    (hAabv : hAab.isIndex v) : v p (a p.z.1) ≤ v p (b p.z.1) := by
  refine Pi.div_mul_cancel_of_forall_imp hab ▸ p.map_mul_apply_of_pi_valuation v _ b ▸
    (mul_le_iff_le_one_left ?_).2 ?_
  · exact (v p).pos_iff.2 fun hbp => hap (hab p.z.1 hbp)
  · refine hAabv.forall_le_of_ne p (a / b) ?_ (fun habp => ?_)
    · exact mem_closure_of_mem <| Set.mem_union_right _ rfl
    · exact Or.elim (div_eq_zero_iff.mp habp) hap (fun hbp => hap (hab p.z.1 hbp))

lemma ne_zero_of_pi_valuation_of_v_extension_of_map_apply_eq {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {a b : Π x : X, i x} (hab : ∀ x : X, b x = 0 → a x = 0)
    {p : σ(X)} (hap : a p.z.1 ≠ 0) {hAab : SpringLike' (Subring.closure (A ∪ {a / b}))}
    (hAabv : hAab.isIndex v) (hvpab : v p (a p.z.1) = v p (b p.z.1)) :
    a p.z.2 ≠ 0 := by
  intro h
  have h1 : (a / b) p.z.2 = 0 := Pi.div_apply a b p.z.2 ▸ h ▸ zero_div (b p.z.2)
  have h2 : (a / b) p.z.1 ≠ 0 := fun h => hap <| hab p.z.1 <|
    (or_iff_not_imp_left.1 <| div_eq_zero_iff.1 <| Pi.div_apply a b p.z.1 ▸ h) hap
  have h3 : v p ((a / b) p.z.1) = 1 ↔ (a / b) p.z.2 ≠ 0 :=
    (hAabv.forall_iff_of_ne p (a / b) (mem_closure_of_mem <| Set.mem_union_right _ rfl) h2)
  have h4 : v p ((a / b) p.z.1) = 1 :=
    (v p).map_div (a p.z.1) (b p.z.1) ▸
      (div_eq_one_iff_eq (hvpab ▸ (v p).ne_zero_iff.2 hap)).2 hvpab
  exact h3.1 h4 h1

end MemClosurePairs

theorem Subring.exists_polynomial_of_mem_closure
    {R : Type*} [CommRing R] {A : Subring R} {x y : R} (hy : y ∈ closure (A.carrier ∪ {x})) :
    ∃ p : Polynomial R, p.eval x = y ∧ ∀ n : ℕ, p.coeff n ∈ A := by
  refine closure_induction (fun y hy => ?_) ?_ ?_
    (fun y1 y2 hy1 hy2 ⟨p1, hpy1, hp1⟩ ⟨p2, hpy2, hp2⟩ => ?_) (fun y hy ⟨p, hpy, hp⟩ => ?_)
    (fun y1 y2 hy1 hy2 ⟨p1, hpy1, hp1⟩ ⟨p2, hpy2, hp2⟩ => ?_) hy
  · by_cases hyx : y = x
    · exact hyx.symm ▸ ⟨X, eval_X,
        fun n => coeff_X (R := R) ▸ ite_mem.mpr ⟨fun hn => one_mem A, fun hn => zero_mem A⟩⟩
    · exact ⟨C y, eval_C,
        fun n => coeff_C (R := R) ▸
          ite_mem.mpr ⟨fun hn => or_iff_not_imp_right.1 hy hyx, fun hn => zero_mem A⟩⟩
  · exact ⟨0, eval_zero, fun n => coeff_zero (R := R) n ▸ zero_mem A⟩
  · exact ⟨1, eval_one, fun n =>
      coeff_one (R := R) ▸ ite_mem.mpr ⟨fun hn => one_mem A, fun hn => zero_mem A⟩⟩
  · exact ⟨p1 + p2, eval_add (R := R) ▸ hpy1 ▸ hpy2 ▸ rfl,
      fun n => coeff_add p1 p2 n ▸ A.add_mem (hp1 n) (hp2 n)⟩
  · exact ⟨-p, hpy ▸ eval_neg p x, fun n => coeff_neg p n ▸ A.neg_mem (hp n)⟩
  · exact ⟨p1 * p2, eval_mul (R := R) ▸ hpy1 ▸ hpy2 ▸ rfl, fun n =>
      coeff_mul p1 p2 n ▸ Subring.sum_mem A fun c hc => Subring.mul_mem A (hp1 c.1) (hp2 c.2)⟩

theorem Subring.exists_polynomial_of_mem_closure₁
    {R : Type*} [CommRing R] {s : Set R} {x y : R} (hy : y ∈ closure (s ∪ {x})) :
    ∃ p : Polynomial R, p.eval x = y ∧ ∀ n : ℕ, p.coeff n ∈ closure s := by
  have : closure (s ∪ {x}) = closure ((closure s) ∪ {x}) :=
    closure_union s {x} ▸ closure_union (closure s) {x} ▸ (closure_eq (closure s)).symm ▸ rfl
  exact exists_polynomial_of_mem_closure (this.symm ▸ hy)

/--
`Subring.repPoly hy = (exists_polynomial_of_mem_closure hy).choose`.
-/
noncomputable def Subring.repPoly {R : Type*} [CommRing R] {A : Subring R} {x y : R}
    (hy : y ∈ closure (A.carrier ∪ {x})) :=
  (exists_polynomial_of_mem_closure hy).choose

lemma Subring.repPoly_eval_eq {R : Type*} [CommRing R] {A : Subring R} {x y : R}
    (hy : y ∈ closure (A.carrier ∪ {x})) : (repPoly hy).eval x = y :=
  (exists_polynomial_of_mem_closure hy).choose_spec.1
