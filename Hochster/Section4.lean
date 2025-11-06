import Mathlib.Data.NNRat.Order
import Mathlib.RingTheory.Valuation.Discrete.Basic

import Hochster.Section3

open CommRing ConstructibleTop Polynomial SpringLike' Subring TopologicalSpace Topology Valuation

section ContentBeforeThm3

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
  exists_forall_eq : ∃ γ : NNRatˣ, ∀ p : σ(X), (forall_isRankOneDiscrete p).generator = γ
  forall_le_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → v p (a p.z.1) ≤ 1
  forall_iff_of_ne (p : σ(X)) : ∀ a ∈ A, a p.z.1 ≠ 0 → (v p (a p.z.1) = 1 ↔ a p.z.2 ≠ 0)
  forall_exists_le : ∀ a ∈ A, ∃ q > (0 : NNRat), ∀ p : σ(X), a p.z.1 ≠ 0 → q ≤ v p (a p.z.1)

theorem Valuation.IsRankOneDiscrete.apply_le_generator_of_apply_lt_one
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {A : Type*} [Ring A]
    {v : Valuation A Γ} [hv : v.IsRankOneDiscrete] {a : A} (hva : v a < 1) :
    v a ≤ hv.generator := by
  by_cases hva0 : v a = 0
  · exact hva0 ▸ zero_le'
  · let va : Γˣ := ⟨v a, (v a)⁻¹, mul_inv_cancel₀ hva0, inv_mul_cancel₀ hva0⟩
    obtain ⟨n, hvn⟩ : va ∈ Subgroup.zpowers hv.generator :=
      hv.exists_generator_lt_one.choose_spec.1 ▸ MonoidWithZeroHom.mem_valueGroup v ⟨a, rfl⟩
    have : va ≤ hv.generator := by
      by_cases hn : 1 ≤ n
      · exact hvn ▸ (Units.val_le_val.1 <| hv.generator.val_zpow_eq_zpow_val 1 ▸
          hv.generator.val_zpow_eq_zpow_val n ▸
          (zpow_le_zpow_iff_right_of_lt_one₀ hv.generator.zero_lt hv.generator_lt_one).2 hn).trans
          ((pow_one hv.generator).symm ▸ le_refl hv.generator)
      · have : 1 ≤ va :=
          hvn ▸ (Units.val_le_val.1 <| Units.val_one (α := Γ) ▸
            hv.generator.val_zpow_eq_zpow_val n ▸
            (one_le_zpow_iff_right_of_lt_one₀ hv.generator.zero_lt hv.generator_lt_one).2
              (not_lt.mp hn))
        exact (not_le_of_gt hva this).elim
    exact this

namespace SpringLike'.isIndex

lemma choose_ne_zero {X : Type*} [TopologicalSpace X] (p : σ(X))
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (hAv : hA.isIndex v) :
    hAv.exists_forall_eq.choose.val ≠ 0 :=
  hAv.exists_forall_eq.choose_spec p ▸ (hAv.forall_isRankOneDiscrete p).generator_ne_zero

lemma choose_lt_one {X : Type*} [TopologicalSpace X] (p : σ(X))
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (hAv : hA.isIndex v) :
    hAv.exists_forall_eq.choose < 1 :=
  hAv.exists_forall_eq.choose_spec p ▸ (hAv.forall_isRankOneDiscrete p).generator_lt_one

lemma choose_ne_one {X : Type*} [TopologicalSpace X] (p : σ(X))
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (hAv : hA.isIndex v) :
    hAv.exists_forall_eq.choose ≠ 1 :=
  ne_of_lt <| choose_lt_one p hAv

lemma map_apply_le_choose_of_apply_ne_zero_of_map_apply_ne_one {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {a : Π x : X, i x} (haA : a ∈ A) {p : σ(X)} (hap : a p.z.1 ≠ 0)
    (hvpa : v p (a p.z.1) ≠ 1) {hA : SpringLike' A} (hAv : hA.isIndex v) :
    v p (a p.z.1) ≤ hAv.exists_forall_eq.choose := by
  obtain ⟨γ, hXγv⟩ := hAv.exists_forall_eq
  obtain ⟨β, hβpv, hβ⟩ := hAv.forall_isRankOneDiscrete p
  exact hAv.exists_forall_eq.choose_spec p ▸
    (hAv.forall_isRankOneDiscrete p).apply_le_generator_of_apply_lt_one <|
      lt_of_le_of_ne (hAv.forall_le_of_ne p a haA hap) hvpa

end SpringLike'.isIndex

end ContentBeforeThm3

section ProvingThm3AndProp1

namespace MemClosurePairs

lemma map_apply_le_of_pi_valuation_of_v_extension {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {a b : Π x : X, i x} (hab : ∀ x : X, b x = 0 → a x = 0)
    {p : σ(X)} (hap : a p.z.1 ≠ 0) {hAab : SpringLike' (closure (A.carrier.insert (a / b)))}
    (hAabv : hAab.isIndex v) : v p (a p.z.1) ≤ v p (b p.z.1) := by
  refine Pi.div_mul_cancel_of_forall_imp hab ▸ p.map_mul_apply_of_pi_valuation v _ b ▸
    (mul_le_iff_le_one_left ?_).2 ?_
  · exact (v p).pos_iff.2 fun hbp => hap (hab p.z.1 hbp)
  · refine hAabv.forall_le_of_ne p (a / b) ?_ (fun habp => ?_)
    · exact mem_closure_of_mem <| A.carrier.mem_insert (a / b)
    · exact Or.elim (div_eq_zero_iff.mp habp) hap (fun hbp => hap (hab p.z.1 hbp))

lemma apply_ne_zero_of_pi_valuation_of_v_extension_of_map_apply_eq {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {a b : Π x : X, i x} (hab : ∀ x : X, b x = 0 → a x = 0)
    {p : σ(X)} (hap : a p.z.1 ≠ 0) {hAab : SpringLike' (closure (A.carrier.insert (a / b)))}
    (hAabv : hAab.isIndex v) (hvpab : v p (a p.z.1) = v p (b p.z.1)) :
    b p.z.2 ≠ 0 := by
  intro h
  have h1 : (a / b) p.z.2 = 0 := Pi.div_apply a b p.z.2 ▸ h.symm ▸ div_zero (a p.z.2)
  have h2 : (a / b) p.z.1 ≠ 0 := fun h => hap <| hab p.z.1 <|
    (or_iff_not_imp_left.1 <| div_eq_zero_iff.1 <| Pi.div_apply a b p.z.1 ▸ h) hap
  have h3 : v p ((a / b) p.z.1) = 1 ↔ (a / b) p.z.2 ≠ 0 :=
    (hAabv.forall_iff_of_ne p (a / b) (mem_closure_of_mem <| A.carrier.mem_insert _) h2)
  have h4 : v p ((a / b) p.z.1) = 1 :=
    (v p).map_div (a p.z.1) (b p.z.1) ▸
      (div_eq_one_iff_eq (hvpab ▸ (v p).ne_zero_iff.2 hap)).2 hvpab
  exact h3.1 h4 h1

end MemClosurePairs

namespace Subring

theorem exists_polynomial_of_mem_closure {R : Type*} [CommRing R] {A : Subring R} {x y : R}
    (hy : y ∈ closure (A.carrier.insert x)) :
    ∃ p : Polynomial R, p.eval x = y ∧ ∀ n : ℕ, p.coeff n ∈ A := by
  refine closure_induction (fun y hy => ?_) ?_ ?_
    (fun y1 y2 hy1 hy2 ⟨p1, hpy1, hp1⟩ ⟨p2, hpy2, hp2⟩ => ?_) (fun y hy ⟨p, hpy, hp⟩ => ?_)
    (fun y1 y2 hy1 hy2 ⟨p1, hpy1, hp1⟩ ⟨p2, hpy2, hp2⟩ => ?_) hy
  · by_cases hyx : y = x
    · exact hyx.symm ▸ ⟨X, eval_X,
        fun n => coeff_X (R := R) ▸ ite_mem.mpr ⟨fun hn => one_mem A, fun hn => zero_mem A⟩⟩
    · exact ⟨C y, eval_C,
        fun n => coeff_C (R := R) ▸
          ite_mem.mpr ⟨fun hn => A.carrier.mem_of_mem_insert_of_ne hy hyx, fun hn => zero_mem A⟩⟩
  · exact ⟨0, eval_zero, fun n => coeff_zero (R := R) n ▸ zero_mem A⟩
  · exact ⟨1, eval_one, fun n =>
      coeff_one (R := R) ▸ ite_mem.mpr ⟨fun hn => one_mem A, fun hn => zero_mem A⟩⟩
  · exact ⟨p1 + p2, eval_add (R := R) ▸ hpy1 ▸ hpy2 ▸ rfl,
      fun n => coeff_add p1 p2 n ▸ A.add_mem (hp1 n) (hp2 n)⟩
  · exact ⟨-p, hpy ▸ eval_neg p x, fun n => coeff_neg p n ▸ A.neg_mem (hp n)⟩
  · exact ⟨p1 * p2, eval_mul (R := R) ▸ hpy1 ▸ hpy2 ▸ rfl, fun n =>
      coeff_mul p1 p2 n ▸ A.sum_mem fun c hc => A.mul_mem (hp1 c.1) (hp2 c.2)⟩

theorem exists_polynomial_of_mem_closure₁ {R : Type*} [CommRing R] {s : Set R} {x y : R}
    (hy : y ∈ closure (s.insert x)) :
    ∃ p : Polynomial R, p.eval x = y ∧ ∀ n : ℕ, p.coeff n ∈ closure s := by
  have : closure (s.insert x) = closure ((closure s).carrier.insert x) := by
    rw [Set.insert, Set.insert]
    exact closure_union {x} s ▸ closure_union {x} (closure s) ▸ (closure_eq (closure s)).symm ▸ rfl
  exact exists_polynomial_of_mem_closure (this ▸ hy)

/--
`Subring.repPoly hy = (Subring.exists_polynomial_of_mem_closure hy).choose`.
-/
noncomputable def repPoly {R : Type*} [CommRing R] {A : Subring R} {x y : R}
    (hy : y ∈ closure (A.carrier.insert x)) :=
  (exists_polynomial_of_mem_closure hy).choose

lemma repPoly_eval_eq {R : Type*} [CommRing R] {A : Subring R} {x y : R}
    (hy : y ∈ closure (A.carrier.insert x)) : (repPoly hy).eval x = y :=
  (exists_polynomial_of_mem_closure hy).choose_spec.1

lemma coeff_repPoly_mem {R : Type*} [CommRing R] {A : Subring R} {x y : R}
    (hy : y ∈ closure (A.carrier.insert x)) (n : ℕ) : (repPoly hy).coeff n ∈ A :=
  (exists_polynomial_of_mem_closure hy).choose_spec.2 n

end Subring

namespace Pi

lemma polynomial_eval_apply {ι : Type*} {G : ι → Type*} [(i : ι) → Semiring (G i)]
    (p : Polynomial ((i : ι) → G i)) (f : (i : ι) → G i) (i : ι) :
    p.eval f i = p.sum fun n g => g i * (f i) ^ n := by
  rw [eval_eq_sum, sum, sum]
  exact Finset.sum_apply i p.support fun n => p.coeff n * f ^ n

lemma polynomial_eval_apply' {ι : Type*} {G : ι → Type*} [(i : ι) → Semiring (G i)]
    (p : Polynomial ((i : ι) → G i)) (f : (i : ι) → G i) (i : ι) :
    p.eval f i = ∑ n ∈ Finset.range (p.natDegree + 1), p.coeff n i * (f i) ^ n := by
  rw [eval_eq_sum_range]
  exact Finset.sum_apply i (Finset.range (p.natDegree + 1)) fun n => p.coeff n * f ^ n

lemma mul_pow_mem_of_mem_closure_insert_div_of_natDegree_repPoly_le
    {ι : Type*} {G : ι → Type*} [(i : ι) → Field (G i)] {A : Subring ((i : ι) → G i)}
    {f g h : (i : ι) → G i} (hf : f ∈ A) (hg : g ∈ A) (hfg : ∀ i : ι, g i = 0 → f i = 0)
    (hh : h ∈ closure (A.carrier.insert (f / g))) {n : ℕ} (hn : (repPoly hh).natDegree ≤ n) :
    h * g ^ n ∈ A := by
  have : h * g ^ n = ((repPoly hh).eval (f / g)) * g ^ n :=
    congrFun (congrArg _ (repPoly_eval_eq hh).symm) _
  exact this ▸ eval_eq_sum (R := Π i : ι, G i) ▸
    sum_def (S := Π i : ι, G i) (repPoly hh) _ ▸ Finset.sum_mul (R := Π i : ι, G i) .. ▸
    A.sum_mem fun m hmh => mul_assoc ((repPoly hh).coeff m) .. ▸
      (Nat.add_sub_of_le <| (le_natDegree_of_mem_supp m hmh).trans hn) ▸ pow_add g m _ ▸
      mul_assoc _ (g ^ m) _ ▸ mul_pow _ g m ▸ mul_mem (coeff_repPoly_mem hh m)
        (mul_mem (pow_mem ((div_mul_cancel_of_forall_imp hfg).symm ▸ hf) m) (pow_mem hg _))

lemma constantCoeff_repPoly_apply_ne_zero_of_apply_eq_zero_of_apply_ne_zero
    {ι : Type*} {i : ι} {G : ι → Type*} [(i : ι) → Field (G i)]
    {A : Subring ((i : ι) → G i)} {f g h : (i : ι) → G i}
    (hfi : f i = 0) (hhi : h i ≠ 0) (hh : h ∈ closure (A.carrier.insert (f / g))) :
    (repPoly hh).constantCoeff i ≠ 0 := by
  have := repPoly_eval_eq hh ▸ hhi
  simp only [polynomial_eval_apply, div_apply, hfi, zero_div, zero_pow_eq, sum, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', ne_eq, ite_eq_right_iff, Classical.not_imp] at this
  exact this.2

lemma mul_pow_natDegree_repPoly_apply_ne_zero_of_apply_ne_zero_of_apply_ne_zero
    {ι : Type*} {i : ι} {G : ι → Type*} [(i : ι) → Field (G i)]
    {A : Subring ((i : ι) → G i)} {f g h : (i : ι) → G i}
    (hgi : g i ≠ 0) (hhi : h i ≠ 0) (hh : h ∈ closure (A.carrier.insert (f / g))) :
    (h * g ^ (repPoly hh).natDegree) i ≠ 0 := by
  simp only [mul_apply, pow_apply, ne_eq, mul_eq_zero, pow_eq_zero_iff', not_or, not_and]
  exact ⟨hhi, fun hgi' _ => hgi hgi'⟩

lemma support_eq_inter_union_inter_of_mem_closure_insert_div
    {ι : Type*} {G : ι → Type*} [(i : ι) → Field (G i)] {A : Subring ((i : ι) → G i)}
    {f g h : (i : ι) → G i} (hfg : ∀ i : ι, g i = 0 → f i = 0)
    (hh : h ∈ closure (A.carrier.insert (f / g))) :
    { i : ι | h i ≠ 0 } =
      ({ i : ι | (h * g ^ (repPoly hh).natDegree) i ≠ 0 } ∩ { i : ι | f i ≠ 0 }) ∪
        ({ i : ι | (repPoly hh).constantCoeff i ≠ 0 } ∩ { i : ι | f i = 0 }) := by
  ext i
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · by_cases hfi : f i = 0
    · exact Or.intro_right _
        ⟨constantCoeff_repPoly_apply_ne_zero_of_apply_eq_zero_of_apply_ne_zero hfi hi hh, hfi⟩
    · exact Or.intro_left _
        ⟨mul_pow_natDegree_repPoly_apply_ne_zero_of_apply_ne_zero_of_apply_ne_zero
          (fun hgi => hfi <| hfg i hgi) hi hh, hfi⟩
  · refine hi.elim (fun ⟨hhgi, hfi⟩ hhi => ?_) (fun ⟨hhi, hfi⟩ => repPoly_eval_eq hh ▸ ?_)
    · exact (zero_mul ((g ^ _) i) ▸ hhi ▸ mul_apply h _ i ▸ Set.mem_setOf_eq ▸ hhgi) rfl
    · simp only [polynomial_eval_apply, sum, div_apply, ne_eq, Set.mem_setOf_eq,
        Set.mem_setOf_eq ▸ hfi, zero_div, zero_pow_eq, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', mem_support_iff, ite_eq_right_iff, Classical.not_imp]
      exact ⟨fun hh0 => hhi (congrFun hh0 i), hhi⟩

lemma constantCoeff_repPoly_apply_eq_zero_of_apply_eq_zero_of_apply_eq_zero
    {ι : Type*} {i : ι} {G : ι → Type*} [(i : ι) → Field (G i)]
    {A : Subring ((i : ι) → G i)} {f g h : (i : ι) → G i}
    (hfi : f i = 0) (hhi : h i = 0) (hh : h ∈ closure (A.carrier.insert (f / g))) :
    (repPoly hh).constantCoeff i = 0 := by
  have := polynomial_eval_apply (repPoly hh) (f / g) i ▸ repPoly_eval_eq hh ▸ hhi
  simp only [sum, div_apply, hfi, zero_div, zero_pow_eq, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', mem_support_iff, ite_eq_right_iff] at this
  exact by_cases (fun hh0 => (repPoly hh).constantCoeff_apply ▸ congrFun hh0 i) this

lemma mul_pow_natDegree_repPoly_apply_eq_zero_of_apply_eq_zero
    {ι : Type*} {i : ι} {G : ι → Type*} [(i : ι) → Field (G i)]
    {A : Subring ((i : ι) → G i)} {f g h : (i : ι) → G i}
    (hhi : h i = 0) (hh : h ∈ closure (A.carrier.insert (f / g))) :
    (h * g ^ (repPoly hh).natDegree) i = 0 := by
  simpa only [mul_apply, mul_eq_zero] using Or.intro_left _ hhi

lemma vanishing_set_eq_inter_union_inter_of_mem_closure_insert_div
    {ι : Type*} {G : ι → Type*} [(i : ι) → Field (G i)] {A : Subring ((i : ι) → G i)}
    {f g h : (i : ι) → G i} (hfg : ∀ i : ι, g i = 0 → f i = 0)
    (hh : h ∈ closure (A.carrier.insert (f / g))) :
    { i : ι | h i = 0 } =
      ({ i : ι | (h * g ^ (repPoly hh).natDegree) i = 0 } ∩ { i : ι | f i ≠ 0 }) ∪
        ({ i : ι | (repPoly hh).constantCoeff i = 0 } ∩ { i : ι | f i = 0 }) := by
  ext i
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · by_cases hfi : f i = 0
    · exact Or.intro_right _
        ⟨constantCoeff_repPoly_apply_eq_zero_of_apply_eq_zero_of_apply_eq_zero hfi hi hh, hfi⟩
    · exact Or.intro_left _ ⟨mul_pow_natDegree_repPoly_apply_eq_zero_of_apply_eq_zero hi hh, hfi⟩
  · refine hi.elim (fun ⟨hhgi, hfi⟩ => ?_) (fun ⟨hhi, hfi⟩ => ?_)
    · exact eq_zero_of_ne_zero_of_mul_right_eq_zero (pow_ne_zero _ (fun hgi => hfi <| hfg i hgi))
        (mul_apply h _ i ▸ Set.mem_setOf_eq ▸ hhgi)
    · refine repPoly_eval_eq hh ▸ ?_
      · simpa only [polynomial_eval_apply, sum, div_apply, Set.mem_setOf_eq, Set.mem_setOf_eq ▸ hfi,
          zero_div, zero_pow_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_eq_right_iff]
            using fun _ => hhi

lemma vanishing_set_eq_inter_union_inter_of_mem_closure_insert_div₁
    {ι : Type*} {G : ι → Type*} [(i : ι) → Field (G i)] {A : Subring ((i : ι) → G i)}
    {f g h : (i : ι) → G i} (hfg : ∀ i : ι, g i = 0 → f i = 0)
    (hh : h ∈ closure (A.carrier.insert (f / g))) :
    { i : ι | h i = 0 } =
      ({ i : ι | (h * g ^ (repPoly hh).natDegree) i = 0 } ∩ { i : ι | g i ≠ 0 }) ∪
        ({ i : ι | (repPoly hh).constantCoeff i = 0 } ∩ { i : ι | g i = 0 }) := by
  ext i
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · by_cases hgi : g i = 0
    · exact Or.intro_right _
        ⟨constantCoeff_repPoly_apply_eq_zero_of_apply_eq_zero_of_apply_eq_zero (hfg i hgi) hi hh,
          hgi⟩
    · exact Or.intro_left _ ⟨mul_pow_natDegree_repPoly_apply_eq_zero_of_apply_eq_zero hi hh, hgi⟩
  · refine hi.elim (fun ⟨hhgi, hgi⟩ => ?_) (fun ⟨hhi, hgi⟩ => ?_)
    · exact eq_zero_of_ne_zero_of_mul_right_eq_zero (pow_ne_zero _ hgi)
        (mul_apply h _ i ▸ Set.mem_setOf_eq ▸ hhgi)
    · refine repPoly_eval_eq hh ▸ ?_
      · simpa only [polynomial_eval_apply, sum, div_apply, Set.mem_setOf_eq, hfg i hgi, zero_div,
          zero_pow_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_eq_right_iff]
            using fun _ => hhi

end Pi

namespace SpringLike'

lemma support_is_patch_of_mem_closure_insert_div
    {X : Type*} [TopologicalSpace X] {i : X → Type*}[(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} (hA : SpringLike' A) {a b r : Π x : X, i x}
    (ha : a ∈ A) (hb : b ∈ A) (hab : ∀ x : X, b x = 0 → a x = 0)
    (hr : r ∈ closure (A.carrier.insert (a / b))) :
    IsClosed (X := ConstructibleTop X) { x : X | r x ≠ 0 } := by
  haveI := hA.spectralSpace
  refine instTopologicalSpace_eq_generateFrom_isOpen_isCompact_union_compl_image X ▸
    Pi.support_eq_inter_union_inter_of_mem_closure_insert_div hab hr ▸
    @IsClosed.union X _ _ (generateFrom _) ?_ ?_
  · refine @IsClosed.inter X _ _ (generateFrom _) ?_ ?_
    · exact (@isOpen_compl_iff X _ (generateFrom _)).1 <| isOpen_generateFrom_of_mem <|
        Or.intro_right _ ⟨{ x | (r * b ^ (repPoly hr).natDegree) x ≠ 0 },
          ⟨hA.forall_isOpen _ <| Pi.mul_pow_mem_of_mem_closure_insert_div_of_natDegree_repPoly_le
            ha hb hab hr <| Nat.le_refl _, hA.forall_isCompact _ <|
              Pi.mul_pow_mem_of_mem_closure_insert_div_of_natDegree_repPoly_le ha hb hab hr <|
                Nat.le_refl _⟩, rfl⟩
    · exact (@isOpen_compl_iff X _ (generateFrom _)).1 <| isOpen_generateFrom_of_mem <|
        Or.intro_right _ ⟨{ x | a x ≠ 0}, ⟨hA.forall_isOpen _ ha, hA.forall_isCompact _ ha⟩, rfl⟩
  · refine @IsClosed.inter X _ _ (generateFrom _) ?_ ?_
    · exact (@isOpen_compl_iff X _ (generateFrom _)).1 <| isOpen_generateFrom_of_mem <|
        Or.intro_right _ ⟨{ x | constantCoeff (repPoly hr) x ≠ 0},
          ⟨hA.forall_isOpen _ (coeff_repPoly_mem hr 0),
            hA.forall_isCompact _ (coeff_repPoly_mem hr 0)⟩, rfl⟩
    · exact (@isOpen_compl_iff X _ (generateFrom _)).1 <| isOpen_generateFrom_of_mem <|
        Or.intro_left _ ⟨hA.forall_isOpen a ha, hA.forall_isCompact a ha⟩

lemma isCompact_support_of_mem_closure_insert_div
    {X : Type*} [TopologicalSpace X] {i : X → Type*}[(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} (hA : SpringLike' A) {a b r : Π x : X, i x}
    (ha : a ∈ A) (hb : b ∈ A) (hab : ∀ x : X, b x = 0 → a x = 0)
    (hr : r ∈ closure (A.carrier.insert (a / b))) :
    IsCompact { x : X | r x ≠ 0 } := by
  haveI := hA.spectralSpace
  exact isCompact_iff_compactSpace.mpr ((Subtype.range_coe_subtype ▸
    compactSpace_of_isEmbedding_of_isClosed_constructibleTop_range IsEmbedding.subtypeVal)
      (support_is_patch_of_mem_closure_insert_div hA ha hb hab hr))

lemma vanishing_set_is_patch_of_mem_closure_insert_div
    {X : Type*} [TopologicalSpace X] {i : X → Type*}[(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} (hA : SpringLike' A) {a b r : Π x : X, i x}
    (ha : a ∈ A) (hb : b ∈ A) (hab : ∀ x : X, b x = 0 → a x = 0)
    (hr : r ∈ closure (A.carrier.insert (a / b))) :
    IsClosed (X := ConstructibleTop X) { x : X | r x = 0 } := by
  haveI := hA.spectralSpace
  refine instTopologicalSpace_eq_generateFrom_isOpen_isCompact_union_compl_image X ▸
    Pi.vanishing_set_eq_inter_union_inter_of_mem_closure_insert_div hab hr ▸
    @IsClosed.union X _ _ (generateFrom _) ?_ ?_
  · refine @IsClosed.inter X _ _ (generateFrom _) ?_ ?_
    · exact (@isOpen_compl_iff X _ (generateFrom _)).1 <| isOpen_generateFrom_of_mem <|
        Or.intro_left _ ⟨hA.forall_isOpen _ <|
          Pi.mul_pow_mem_of_mem_closure_insert_div_of_natDegree_repPoly_le ha hb hab hr <|
            Nat.le_refl _, hA.forall_isCompact _ <|
              Pi.mul_pow_mem_of_mem_closure_insert_div_of_natDegree_repPoly_le ha hb hab hr <|
                Nat.le_refl _⟩
    · exact (@isOpen_compl_iff X _ (generateFrom _)).1 <| isOpen_generateFrom_of_mem <|
        Or.intro_right _ ⟨{ x | a x ≠ 0}, ⟨hA.forall_isOpen _ ha, hA.forall_isCompact _ ha⟩, rfl⟩
  · refine @IsClosed.inter X _ _ (generateFrom _) ?_ ?_
    · exact (@isOpen_compl_iff X _ (generateFrom _)).1 <| isOpen_generateFrom_of_mem <|
        Or.intro_left _ ⟨hA.forall_isOpen _ (coeff_repPoly_mem hr 0),
          hA.forall_isCompact _ (coeff_repPoly_mem hr 0)⟩
    · exact (@isOpen_compl_iff X _ (generateFrom _)).1 <| isOpen_generateFrom_of_mem <|
        Or.intro_left _ ⟨hA.forall_isOpen a ha, hA.forall_isCompact a ha⟩

lemma isCompact_vanishing_set_of_mem_closure_insert_div
    {X : Type*} [TopologicalSpace X] {i : X → Type*}[(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} (hA : SpringLike' A) {a b r : Π x : X, i x}
    (ha : a ∈ A) (hb : b ∈ A) (hab : ∀ x : X, b x = 0 → a x = 0)
    (hr : r ∈ closure (A.carrier.insert (a / b))) :
    IsCompact { x : X | r x = 0 } := by
  haveI := hA.spectralSpace
  exact isCompact_iff_compactSpace.mpr ((Subtype.range_coe_subtype ▸
    compactSpace_of_isEmbedding_of_isClosed_constructibleTop_range IsEmbedding.subtypeVal)
      (vanishing_set_is_patch_of_mem_closure_insert_div hA ha hb hab hr))

end SpringLike'

lemma isClosed_iff_forall_closure_subset_of_isClosed_constructibleTop
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [QuasiSober X] [QuasiSeparatedSpace X]
    [PrespectralSpace X] {Y : Set X} (hY : IsClosed (X := ConstructibleTop X) Y) :
    IsClosed Y ↔ ∀ y ∈ Y, closure {y} ⊆ Y := by
  refine ⟨fun hY y hyY => (IsClosed.mem_iff_closure_subset hY).mp hyY,
    fun h => closure_eq_iff_isClosed.1 <| Set.eq_of_subset_of_subset ?_ subset_closure⟩
  · intro y hyY
    obtain ⟨x, hxY, hyx⟩ := (mem_patch_closure_iff_mem_pt_closure hY y).1 hyY
    exact h x hxY hyx

namespace SpringLike'.isIndex

lemma isClosed_vanishing_set_of_forall_map_apply_le_of_forall_ne_zero
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) {a b r : Π x : X, i x} (ha : a ∈ A) (hb : b ∈ A)
    (hab : ∀ x : X, b x = 0 → a x = 0) (hr : r ∈ closure (A.carrier.insert (a / b)))
    (h1 : ∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) ≤ v p (b p.z.1))
    (h2 : ∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) = v p (b p.z.1) → b p.z.2 ≠ 0) :
    IsClosed { x : X | r x = 0 } := by
  haveI := hA.spectralSpace
  refine (isClosed_iff_forall_closure_subset_of_isClosed_constructibleTop (X := X)
    (hA.vanishing_set_is_patch_of_mem_closure_insert_div ha hb hab hr)).2 fun y hry => ?_
  · by_cases hay : a y = 0
    · refine Pi.vanishing_set_eq_inter_union_inter_of_mem_closure_insert_div hab hr ▸
        Set.subset_union_of_subset_right ((IsClosed.closure_subset_iff ?_).2 ?_) _
      · exact IsClosed.inter ⟨hA.forall_isOpen _ (coeff_repPoly_mem hr 0)⟩ ⟨hA.forall_isOpen _ ha⟩
      · exact Set.singleton_subset_iff.2
          ⟨Pi.constantCoeff_repPoly_apply_eq_zero_of_apply_eq_zero_of_apply_eq_zero hay hry hr, hay⟩
    · intro x hxy
      by_cases hbx : b x = 0
      · let p : σ(X) := ⟨(y, x), hxy⟩
        have hvpab := lt_of_le_of_ne (h1 p hay) (imp_not_comm.1 (h2 p hay) hbx)
        have habry : -((repPoly hr).coeff 0 y * b y ^ (repPoly hr).natDegree) =
            ∑ n ∈ Finset.range ((repPoly hr).natDegree + 1) \ {0},
              (repPoly hr).coeff n y * a y ^ n * b y ^ ((repPoly hr).natDegree - n) := by
          have := mul_eq_zero_of_left ((Finset.sum_sdiff (f := fun n =>
            (repPoly hr).coeff n y * (a / b) y ^ n) <| Finset.singleton_subset_iff.mpr <|
            Finset.mem_range.mpr <| (1 : ℕ).le_add_left _) ▸ Pi.polynomial_eval_apply' (repPoly hr)
              _ y ▸ Set.mem_setOf_eq ▸ repPoly_eval_eq hr ▸ hry) (b y ^ (repPoly hr).natDegree)
          simp only [add_mul, add_eq_zero_iff_neg_eq', Finset.sum_singleton, pow_zero, mul_one,
            Finset.sum_mul] at this
          exact this ▸ Finset.sum_congr rfl fun n hn => mul_assoc ((repPoly hr).coeff n y) .. ▸
            (mul_assoc ((repPoly hr).coeff n y) ..).symm ▸ (Nat.add_sub_of_le <|
              Finset.mem_range_succ_iff.1 (Finset.mem_sdiff.1 hn).1) ▸ Nat.add_sub_self_left .. ▸
              pow_add (b y) .. ▸ mul_assoc ((a y / _) ^ n) .. ▸ mul_pow (a y / _) .. ▸
              (div_mul_cancel₀ (a y) (fun hby => hay <| hab y hby)).symm ▸ rfl
        have hvpbry : v p (-((repPoly hr).coeff 0 y * b y ^ (repPoly hr).natDegree)) <
            (v p (b y)) ^ (repPoly hr).natDegree := by
          refine habry ▸ map_sum_lt (v p) (pow_ne_zero _ <| (ne_zero_iff (v p)).2
            fun hby => hay <| hab y hby) fun n hn => map_mul (v p) .. ▸ (map_mul (v p) ..).symm ▸
              (v p).map_pow _ (_ - n) ▸ ?_
          · by_cases hrny : (repPoly hr).coeff n y = 0
            · exact hrny ▸ (v p).map_zero ▸ (zero_mul (v p _)).symm ▸ (zero_mul ((v p _) ^ _)).symm
                ▸ pow_pos ((pos_iff (v p)).2 fun hby => hay <| hab y hby) _
            · refine mul_assoc (v p _) .. ▸ lt_of_le_of_lt
                (mul_le_of_le_one_left (zero_le (_ * (v p) _ ^ _))
                  (hAv.forall_le_of_ne p _ (coeff_repPoly_mem hr n) hrny))
                ((Nat.add_sub_of_le <| le_natDegree_of_ne_zero fun hrn =>
                  hrny (congrFun hrn y)) ▸ Nat.add_sub_cancel_left .. ▸ pow_add (v p _) .. ▸
                  (v p).map_pow (a y) n ▸ mul_lt_mul_of_pos_right ?_ ?_)
              · exact (pow_lt_pow_iff_left₀ (zero_le _) (zero_le _) <|
                  Finset.notMem_singleton.1 (Finset.mem_sdiff.1 hn).2).2 hvpab
              · exact pow_pos (lt_of_le_of_ne (zero_le _)
                  (ne_of_lt <| lt_of_le_of_lt (zero_le _) hvpab)) _
        by_cases hry0 : (repPoly hr).coeff 0 y = 0
        · exact Pi.vanishing_set_eq_inter_union_inter_of_mem_closure_insert_div₁ hab hr ▸
            Or.intro_right _ ⟨(⟨hA.forall_isOpen (constantCoeff (repPoly hr))
              (coeff_repPoly_mem hr 0)⟩ : IsClosed _).mem_iff_closure_subset.1 hry0 hxy, hbx⟩
        · refine Pi.vanishing_set_eq_inter_union_inter_of_mem_closure_insert_div₁ hab hr ▸
            Or.intro_right _ ⟨?_, hbx⟩
          · exact (iff_not_comm.1 <| hAv.forall_iff_of_ne p ((repPoly hr).coeff 0)
              (coeff_repPoly_mem hr 0) hry0).2 <| ne_of_lt <| lt_one_of_mul_lt_left <|
                (v p).map_pow .. ▸ (v p).map_mul .. ▸ (v p).map_neg _ ▸ hvpbry
      · exact Pi.vanishing_set_eq_inter_union_inter_of_mem_closure_insert_div₁ hab hr ▸
          Or.intro_left _ ⟨(IsClosed.mem_iff_closure_subset ⟨hA.forall_isOpen _ <|
            Pi.mul_pow_mem_of_mem_closure_insert_div_of_natDegree_repPoly_le ha hb hab hr <|
              Nat.le_refl _⟩).1 (Pi.mul_pow_natDegree_repPoly_apply_eq_zero_of_apply_eq_zero hry hr)
                hxy, hbx⟩

def closureInsertDiv {X : Type*} [TopologicalSpace X] {i : X → Type*}
    [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (hAv : hA.isIndex v)
    {a b : Π x : X, i x} (ha : a ∈ A) (hb : b ∈ A) (hab : ∀ x : X, b x = 0 → a x = 0)
    (h1 : ∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) ≤ v p (b p.z.1))
    (h2 : ∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) = v p (b p.z.1) → b p.z.2 ≠ 0) :
    SpringLike' (closure (A.carrier.insert (a / b))) :=
  hA.springLike'_closure_union_of_forall_isOpen_isCompact fun _ hr =>
    ⟨(hAv.isClosed_vanishing_set_of_forall_map_apply_le_of_forall_ne_zero ha hb hab hr h1 h2).1,
      hA.isCompact_support_of_mem_closure_insert_div ha hb hab hr⟩

lemma map_apply_le_one_of_mem_closure_insert_div_of_forall_map_apply_le
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) {a b r : Π x : X, i x}
    (hab : ∀ x : X, b x = 0 → a x = 0) (hr : r ∈ closure (A.carrier.insert (a / b)))
    {p : σ(X)} (hrp : r p.z.1 ≠ 0) (h : ∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) ≤ v p (b p.z.1)) :
    v p (r p.z.1) ≤ 1 := by
  refine repPoly_eval_eq hr ▸ Pi.polynomial_eval_apply (repPoly hr) (a / b) p.z.1 ▸
    Or.elim (Pi.support_eq_inter_union_inter_of_mem_closure_insert_div hab hr ▸
    Set.mem_setOf_eq (p := fun y => r y ≠ 0) ▸ hrp) (fun ⟨hbrp, hap⟩ => ?_) (fun ⟨hrp, hap⟩ => ?_)
  · refine (v p).map_sum_le fun n hnr => (v p).map_mul .. ▸ (v p).map_pow .. ▸ (v p).map_div .. ▸ ?_
    · by_cases hrnp : (repPoly hr).coeff n p.z.1 = 0
      · exact hrnp ▸ (v p).map_zero ▸ (zero_mul ((v p _ / _) ^ n)).symm ▸ rfl
      · exact mul_le_one' (hAv.forall_le_of_ne p ((repPoly hr).coeff n) (coeff_repPoly_mem hr n)
          hrnp) (pow_le_one' ((div_le_one <| lt_of_lt_of_le ((v p).pos_iff.2 hap) (h p hap)).2
            (h p hap)) _)
  · simp only [sum, Pi.div_apply, Set.mem_setOf_eq ▸ hap, zero_div, zero_pow_eq, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq']
    by_cases h0 : 0 ∈ (repPoly hr).support
    · simpa only [h0] using hAv.forall_le_of_ne p _ (coeff_repPoly_mem hr 0) hrp
    · simp [h0, reduceIte, map_zero]

lemma false_of_apply_eq_zero_of_apply_ne_zero {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (hAv : hA.isIndex v) {a b : Π x : X, i x}
    (ha : a ∈ A) (hb : b ∈ A) {p : σ(X)} (hap1 : a p.z.1 = 0) (hap2 : a p.z.2 ≠ 0)
    (hbp1 : b p.z.1 ≠ 0) (hbp2 : b p.z.2 = 0) : False := by
  have : v p ((a + b) p.z.1) = 1 :=
    (hAv.forall_iff_of_ne p (a + b) (add_mem ha hb)
      (Pi.add_apply a .. ▸ hap1.symm ▸ (zero_add (b p.z.1)).symm ▸ hbp1)).2
        (Pi.add_apply a .. ▸ hbp2.symm ▸ (add_zero (a p.z.2)).symm ▸ hap2)
  have : v p (b p.z.1) = 1 := zero_add (b p.z.1) ▸ hap1 ▸ Pi.add_apply a .. ▸ this
  exact (hAv.forall_iff_of_ne p b hb hbp1).1 this hbp2

lemma map_apply_eq_one_iff_apply_ne_zero_of_forall_map_apply_le_of_forall_ne_zero
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) {a b r : Π x : X, i x} (ha : a ∈ A) (hb : b ∈ A)
    (hab : ∀ x : X, b x = 0 → a x = 0) (hr : r ∈ closure (A.carrier.insert (a / b)))
    {p : σ(X)} (hrp : r p.z.1 ≠ 0) (h1 : ∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) ≤ v p (b p.z.1))
    (h2 : ∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) = v p (b p.z.1) → b p.z.2 ≠ 0) :
    v p (r p.z.1) = 1 ↔ r p.z.2 ≠ 0 := by
  refine Or.elim (Pi.support_eq_inter_union_inter_of_mem_closure_insert_div hab hr ▸
    Set.mem_setOf_eq (p := fun y => r y ≠ 0) ▸ hrp) (fun ⟨hbrp, hap⟩ => ?_) (fun ⟨hrp, hap⟩ => ?_)
  · have hvpb : v p (b p.z.1) ≠ 0 := (v p).ne_zero_iff.2 fun hbp => hap <| hab p.z.1 hbp
    have h3 (hvpab : v p (a p.z.1) = v p (b p.z.1)) : v p (b p.z.1) = 1 :=
      (hAv.forall_iff_of_ne p b hb <| (v p).ne_zero_iff.1 hvpb).2 (h2 p hap hvpab)
    have h4 (hvpab : v p (a p.z.1) ≠ v p (b p.z.1)) : a p.z.2 = 0 :=
      (iff_not_comm.1 <| hAv.forall_iff_of_ne p a ha hap).2 <| ne_of_lt <| lt_of_lt_of_le
        (lt_of_le_of_ne (h1 p hap) hvpab) (hAv.forall_le_of_ne p b hb fun hbp =>
          hap <| hab p.z.1 hbp)
    refine ⟨fun hvpr => ?_, fun hrp0 => ?_⟩
    · by_cases hvpab : v p (a p.z.1) = v p (b p.z.1)
      · have : v p ((r * b ^ (repPoly hr).natDegree) p.z.1) = 1 :=
          (v p).map_mul .. ▸ hvpr.symm ▸ (one_mul (v p _)).symm ▸
            Pi.pow_apply b (repPoly hr).natDegree p.z.1 ▸ (v p).map_pow .. ▸ (h3 hvpab).symm ▸
            one_pow _
        have : (r * b ^ (repPoly hr).natDegree) p.z.2 ≠ 0 :=
          (hAv.forall_iff_of_ne p (r * b ^ (repPoly hr).natDegree)
            (Pi.mul_pow_mem_of_mem_closure_insert_div_of_natDegree_repPoly_le ha hb hab hr
              (repPoly hr).natDegree.le_refl) ((v p).ne_zero_iff.1 <| ne_zero_of_eq_one this)).1
              this
        exact (mul_ne_zero_iff.1 <| Pi.mul_apply r .. ▸ this).1
      · have hvpr1 : v p ((repPoly hr).coeff 0 p.z.1) = 1 := by
          by_contra hvpr1
          · have : v p ((repPoly hr).coeff 0 p.z.1) < 1 := by
              by_cases hr0 : (repPoly hr).coeff 0 p.z.1 = 0
              · exact hr0 ▸ (v p).map_zero ▸ rfl
              · exact lt_of_le_of_ne (hAv.forall_le_of_ne p ((repPoly hr).coeff 0)
                  (coeff_repPoly_mem hr 0) hr0) hvpr1
            have : v p (r p.z.1) < 1 := by
              refine repPoly_eval_eq hr ▸ Pi.polynomial_eval_apply (repPoly hr) .. ▸
                (v p).map_sum_lt (zero_ne_one' _).symm fun n hnr =>
                (v p).map_mul ((repPoly hr).coeff _ _) _ ▸ (v p).map_pow .. ▸ Pi.div_apply a .. ▸ ?_
              · by_cases hn0 : n = 0
                · exact hn0 ▸ (pow_zero (v p _)).symm ▸ (mul_one (v p _)).symm ▸ this
                · refine mul_lt_one_of_nonneg_of_lt_one_right ?_ (zero_le _) ?_
                  · by_cases hrnp : (repPoly hr).coeff n p.z.1 = 0
                    · exact hrnp ▸ (v p).map_zero ▸ rfl
                    · exact hAv.forall_le_of_ne p ((repPoly hr).coeff n) (coeff_repPoly_mem hr n)
                        hrnp
                  · exact pow_lt_one₀ (zero_le _) ((v p).map_div .. ▸ (div_lt_one₀ <|
                      lt_of_le_of_lt (zero_le _) (lt_of_le_of_ne (h1 p hap) hvpab)).2 <|
                        lt_of_le_of_ne (h1 p hap) hvpab) hn0
            exact (lt_self_iff_false 1).1 <| hvpr ▸ this
        have hrp0 : (repPoly hr).coeff 0 p.z.2 ≠ 0 :=
          (hAv.forall_iff_of_ne p ((repPoly hr).coeff 0) (coeff_repPoly_mem hr 0)
            (((v p).ne_zero_iff).1 <| ne_zero_of_eq_one hvpr1)).1 hvpr1
        refine repPoly_eval_eq hr ▸ ?_
        · simp only [Pi.polynomial_eval_apply, sum, Pi.div_apply, h4 hvpab, zero_div, zero_pow_eq,
            mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_support_iff, ne_eq,
            ite_eq_right_iff, Classical.not_imp]
          exact ⟨fun hr0 => (hr0 ▸ hrp0) rfl, hrp0⟩
    · by_cases hvpab : v p (a p.z.1) = v p (b p.z.1)
      · have : (r * b ^ (repPoly hr).natDegree) p.z.2 ≠ 0 :=
          Pi.mul_apply r .. ▸ Pi.pow_apply b (repPoly hr).natDegree _ ▸
            mul_ne_zero hrp0 (pow_ne_zero _ <| h2 p hap hvpab)
        have :  v p ((r * b ^ (repPoly hr).natDegree) p.z.1) = 1 :=
          (hAv.forall_iff_of_ne p (r * b ^ (repPoly hr).natDegree)
            (Pi.mul_pow_mem_of_mem_closure_insert_div_of_natDegree_repPoly_le ha hb hab hr
              (repPoly hr).natDegree.le_refl) hbrp).2 this
        simp only [Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, h3 hvpab, one_pow, mul_one] at this
        exact this
      · have hrp2 : (repPoly hr).coeff 0 p.z.2 ≠ 0 := by
          have := repPoly_eval_eq hr ▸ hrp0
          simpa only [Pi.polynomial_eval_apply', Pi.div_apply, h4 hvpab, zero_div, zero_pow_eq,
            mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, add_pos_iff,
            zero_lt_one, or_true] using this
        have hrp1 : (repPoly hr).coeff 0 p.z.1 ≠ 0 := by
          intro h
          have hbrp1 : ((r - (repPoly hr).coeff 0) * b ^ (repPoly hr).natDegree) p.z.1 ≠ 0 :=
            Pi.mul_apply (r - _) .. ▸ Pi.sub_apply r .. ▸ h.symm ▸ (sub_zero (r p.z.1)).symm ▸
              Pi.mul_apply r .. ▸ hbrp
          have hbrp2 : ((r - (repPoly hr).coeff 0) * b ^ (repPoly hr).natDegree) p.z.2 = 0 := by
            refine Pi.mul_apply (r - _) .. ▸ Pi.sub_apply r .. ▸
              mul_eq_zero_of_left (congrFun (repPoly_eval_eq hr).symm p.z.2 ▸ ?_) _
            · simp only [Pi.polynomial_eval_apply', Pi.div_apply, h4 hvpab, zero_div, zero_pow_eq,
                mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, add_pos_iff,
                zero_lt_one, or_true, reduceIte, sub_self]
          have hbrpA : (r - (repPoly hr).coeff 0) * b ^ (repPoly hr).natDegree ∈ A :=
            sub_mul r .. ▸ sub_mem (Pi.mul_pow_mem_of_mem_closure_insert_div_of_natDegree_repPoly_le
              ha hb hab hr (repPoly hr).natDegree.le_refl) (A.mul_mem (coeff_repPoly_mem hr 0)
                (A.pow_mem hb _))
          exact false_of_apply_eq_zero_of_apply_ne_zero hAv (coeff_repPoly_mem hr 0) hbrpA h hrp2
            hbrp1 hbrp2
        have hvpr : v p ((repPoly hr).coeff 0 p.z.1) = 1 :=
          (hAv.forall_iff_of_ne p ((repPoly hr).coeff 0) (coeff_repPoly_mem hr 0) hrp1).2 hrp2
        refine repPoly_eval_eq hr ▸ Pi.polynomial_eval_apply' (repPoly hr) .. ▸ ?_
        · have := (v p).map_sum_eq_of_lt
            (Finset.mem_range.2 <| Nat.zero_lt_succ (repPoly hr).natDegree)
            (f := fun n => (repPoly hr).coeff n p.z.1 * (a / b) p.z.1 ^ n)
          simp only [pow_zero, mul_one, hvpr, ne_eq, one_ne_zero, not_false_eq_true,
            Finset.mem_sdiff, Finset.mem_singleton, map_mul, map_pow, and_imp, forall_const] at this
          refine this fun n hnr hn => ?_
          · by_cases hrnp : (repPoly hr).coeff n p.z.1 = 0
            · exact hrnp ▸ (v p).map_zero ▸ (zero_mul ((v p _) ^ n)).symm ▸ rfl
            · exact Pi.div_apply a .. ▸ (v p).map_div (a _) .. ▸
                mul_lt_one_of_nonneg_of_lt_one_right (hAv.forall_le_of_ne p ((repPoly hr).coeff n)
                  (coeff_repPoly_mem hr n) hrnp) (zero_le _) (pow_lt_one' ((div_lt_one
                    (lt_of_le_of_ne (zero_le _) hvpb.symm)).2 (lt_of_le_of_ne (h1 p hap) hvpab)) hn)
  · refine repPoly_eval_eq hr ▸ ?_
    · have : a p.z.2 = 0 :=
        (IsClosed.closure_subset_iff ⟨hA.forall_isOpen a ha⟩).2 (Set.singleton_subset_iff.mpr hap)
          p.mem_closure
      simp only [Pi.polynomial_eval_apply', Pi.div_apply, Set.mem_setOf_eq ▸ hap, zero_div,
        zero_pow_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, add_pos_iff,
        zero_lt_one, or_true, this]
      exact hAv.forall_iff_of_ne p ((repPoly hr).coeff 0) (coeff_repPoly_mem hr 0) hrp

lemma exists_le_map_apply_of_mem_closure_insert_div
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) {a b r : Π x : X, i x} (ha : a ∈ A) (hb : b ∈ A)
    (hab : ∀ x : X, b x = 0 → a x = 0) (hr : r ∈ closure (A.carrier.insert (a / b))) :
    ∃ s > (0 : NNRat), ∀ p : σ(X), r p.z.1 ≠ 0 → s ≤ v p (r p.z.1) := by
  obtain ⟨s1, hs1, hvrs1⟩ := hAv.forall_exists_le ((repPoly hr).coeff 0) (coeff_repPoly_mem hr 0)
  obtain ⟨s2, hs2, hvbrs2⟩ := hAv.forall_exists_le (r * b ^ (repPoly hr).natDegree)
    (Pi.mul_pow_mem_of_mem_closure_insert_div_of_natDegree_repPoly_le ha hb hab hr
      (repPoly hr).natDegree.le_refl)
  refine ⟨min s1 s2, lt_min (NNRat.cast_pos.2 hs1) (NNRat.cast_pos.2 hs2), fun p hrp => ?_⟩
  · by_cases hbp : b p.z.1 = 0
    · by_cases hrp0 : (repPoly hr).coeff 0 p.z.1 = 0
      · have := repPoly_eval_eq hr ▸ hrp
        simp only [Pi.polynomial_eval_apply', Pi.div_apply, hbp, div_zero, zero_pow_eq, mul_ite,
          mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, add_pos_iff, zero_lt_one,
          or_true] at this
        exact False.elim (this hrp0)
      · refine repPoly_eval_eq hr ▸ ?_
        · simp only [Pi.polynomial_eval_apply', Pi.div_apply, hbp, div_zero, zero_pow_eq, mul_ite,
            mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, add_pos_iff, zero_lt_one,
            or_true, inf_le_iff]
          exact Or.intro_left _ (NNRat.cast_le.2 <| hvrs1 p hrp0)
    · have : s2 ≤ (v p (r p.z.1) * v p (b p.z.1) ^ (repPoly hr).natDegree) :=
        (v p).map_pow .. ▸ Pi.pow_apply b (repPoly hr).natDegree _ ▸ (v p).map_mul .. ▸
          Pi.mul_apply r .. ▸ hvbrs2 p (Pi.mul_apply r .. ▸ Pi.pow_apply b (repPoly hr).natDegree _
            ▸ mul_ne_zero hrp (pow_ne_zero _ hbp))
      have : s2 ≤ v p (r p.z.1) :=
        this.trans <| mul_le_of_le_one_right (v p (r p.z.1)).cast_nonneg <|
          pow_le_one₀ (v p (b p.z.1)).cast_nonneg <| NNRat.cast_le_one.2 <|
            hAv.forall_le_of_ne p b hb hbp
      exact inf_le_of_right_le (NNRat.cast_le.2 this)

lemma closureInsertDiv_isIndex_of_forall_map_apply_le_of_forall_ne_zero
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) {a b : Π x : X, i x}
    (ha : a ∈ A) (hb : b ∈ A) (hab : ∀ x : X, b x = 0 → a x = 0)
    (h1 : ∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) ≤ v p (b p.z.1))
    (h2 : ∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) = v p (b p.z.1) → b p.z.2 ≠ 0) :
    (hAv.closureInsertDiv ha hb hab h1 h2).isIndex v where
  forall_isRankOneDiscrete := hAv.forall_isRankOneDiscrete
  exists_forall_eq := hAv.exists_forall_eq
  forall_le_of_ne _ _ hr hrp := map_apply_le_one_of_mem_closure_insert_div_of_forall_map_apply_le
    hAv hab hr hrp h1
  forall_iff_of_ne _ _ hr hrp :=
    map_apply_eq_one_iff_apply_ne_zero_of_forall_map_apply_le_of_forall_ne_zero hAv ha hb hab hr
      hrp h1 h2
  forall_exists_le _ hr := exists_le_map_apply_of_mem_closure_insert_div hAv ha hb hab hr

/-- This is Theorem 3 in the paper. -/
lemma forall_map_apply_le_and_forall_apply_ne_zero_iff_exists_isIndex
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) {a b : Π x : X, i x}
    (ha : a ∈ A) (hb : b ∈ A) (hab : ∀ x : X, b x = 0 → a x = 0) :
    (∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) ≤ v p (b p.z.1) ∧
      (v p (a p.z.1) = v p (b p.z.1) → b p.z.2 ≠ 0)) ↔
        ∃ hAab : SpringLike' (closure (A.carrier.insert (a / b))), hAab.isIndex v := by
  refine ⟨fun h => ?_, fun ⟨hAab, hAabv⟩ p hap => ?_⟩
  · exact ⟨hAv.closureInsertDiv ha hb hab (fun p hap => (h p hap).1) (fun p hap => (h p hap).2),
      hAv.closureInsertDiv_isIndex_of_forall_map_apply_le_of_forall_ne_zero ha hb hab
        (fun p hap => (h p hap).1) (fun p hap => (h p hap).2)⟩
  · exact ⟨p.map_apply_le_of_pi_valuation_of_v_extension hab hap hAabv, fun hvpab =>
      p.apply_ne_zero_of_pi_valuation_of_v_extension_of_map_apply_eq hab hap hAabv hvpab⟩

lemma exists_isIndex_iff_exists_isIndex_of_subset
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A B : Subring (Π x : X, i x)}
    {hA : SpringLike' A} {hB : SpringLike' B} (hAB : A.carrier ⊆ B.carrier)
    (hAv : hA.isIndex v) (hBv : hB.isIndex v) {a b : Π x : X, i x} (ha : a ∈ A) (hb : b ∈ A)
    (hab : ∀ x : X, b x = 0 → a x = 0) :
    (∃ hAab : SpringLike' (closure (A.carrier.insert (a / b))), hAab.isIndex v) ↔
      (∃ hBab : SpringLike' (closure (B.carrier.insert (a / b))), hBab.isIndex v) :=
  ⟨fun ⟨hAab, hAabv⟩ =>
    (forall_map_apply_le_and_forall_apply_ne_zero_iff_exists_isIndex hBv (hAB ha) (hAB hb) hab).1
      ((forall_map_apply_le_and_forall_apply_ne_zero_iff_exists_isIndex hAv ha hb hab).2
        ⟨hAab, hAabv⟩),
  fun ⟨hBab, hBabv⟩ =>
    (forall_map_apply_le_and_forall_apply_ne_zero_iff_exists_isIndex hAv ha hb hab).1
      ((forall_map_apply_le_and_forall_apply_ne_zero_iff_exists_isIndex hBv (hAB ha) (hAB hb) hab).2
        ⟨hBab, hBabv⟩)⟩

open Classical in
lemma exists_isIndex_of_forall_springLike'_closure_insert_div_of_forall_isIndex
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) {S : Finset ((Π x : X, i x) × (Π x : X, i x))}
    (hSA : ∀ s ∈ S, s.1 ∈ A ∧ s.2 ∈ A) (hSX : ∀ s ∈ S, ∀ x : X, s.2 x = 0 → s.1 x = 0)
    {F : Π s : S, SpringLike' (closure (A.carrier.insert (s.1.1 / s.1.2)))}
    (G : Π s : S, (F s).isIndex v) :
    ∃ hAS : SpringLike' (closure (A.carrier ∪ { s.1 / s.2 | s ∈ S })), hAS.isIndex v := by
  suffices ∀ n (S : Finset ((Π x : X, i x) × (Π x : X, i x)))
    (hSA : ∀ s ∈ S, s.1 ∈ A ∧ s.2 ∈ A) (hSX : ∀ s ∈ S, ∀ x : X, s.2 x = 0 → s.1 x = 0)
    (F : Π s : S, SpringLike' (closure (A.carrier.insert (s.1.1 / s.1.2))))
    (G : Π s : S, (F s).isIndex v), S.card = n →
      ∃ hAS : SpringLike' (closure (A.carrier ∪ { s.1 / s.2 | s ∈ S })), hAS.isIndex v from
        this S.card S hSA hSX F G rfl
  · intro n
    induction n with
    | zero =>
        intro S _ _ _ _ hS0
        simp only [Subsemiring.coe_carrier_toSubmonoid, coe_toSubsemiring, S.card_eq_zero.1 hS0,
          Finset.notMem_empty, false_and, exists_const, Set.setOf_false, Set.union_empty,
          closure_eq]
        use hA
    | succ n hn =>
        intro S hSA hSX F G hSn
        obtain ⟨s, hsS⟩ := (hSn ▸ S.card_ne_zero.1) n.succ_ne_zero
        obtain ⟨hASs, hASsv⟩ : ∃ hASs : SpringLike' (closure (A.carrier ∪
            { a | ∃ t ∈ S \ {s}, t.1 / t.2 = a })), hASs.isIndex v :=
          hn (S \ {s}) (fun t htS => hSA t (S.mem_sdiff.1 htS).1)
            (fun t htS => hSX t (S.mem_sdiff.1 htS).1) (fun ⟨t, htS⟩ => F ⟨t, (S.mem_sdiff.1 htS).1⟩)
            (fun ⟨t, htS⟩ => G ⟨t, (S.mem_sdiff.1 htS).1⟩)
            (add_tsub_cancel_right n 1 ▸ Finset.card_singleton s ▸ hSn ▸
              ({s} : Finset _).card_sdiff_of_subset (S.singleton_subset_iff.mpr hsS))
        have : closure (A ∪ { a | ∃ s ∈ S, s.1 / s.2 = a }) =
            closure ((closure (A ∪ { a | ∃ t ∈ S \ {s}, t.1 / t.2 = a })).carrier.insert
              (s.1 / s.2)) := by
          simp only [Set.insert, ← Set.insert_def, ← Set.union_singleton, closure_union _ {_}]
          erw [(closure (A ∪ { a | ∃ t ∈ S \ {s}, t.1 / t.2 = a })).closure_eq]
          simp only [← closure_union _ {s.1 / s.2}, Set.union_assoc]
          have : { a | ∃ s ∈ S, s.1 / s.2 = a } =
              { a | ∃ t ∈ S \ {s}, t.1 / t.2 = a } ∪ {s.1 / s.2} := by
            ext a
            refine ⟨fun ⟨t, htS, hta⟩ => hta ▸ ?_, fun haSs => Or.elim haSs ?_ ?_⟩
            · by_cases hts : t = s
              · exact hts ▸ Or.intro_right _ rfl
              · exact Or.intro_left _ ⟨t, S.mem_sdiff.2 ⟨htS, Finset.notMem_singleton.2 hts⟩, rfl⟩
            · exact fun ⟨t, htS, hta⟩ => ⟨t, (Finset.mem_sdiff.1 htS).1, hta⟩
            · exact fun has => ⟨s, hsS, (funext <| congrFun has).symm⟩
          exact this ▸ rfl
        exact this ▸ (hASsv.forall_map_apply_le_and_forall_apply_ne_zero_iff_exists_isIndex
          (mem_closure_of_mem <| Or.intro_left _ (hSA s hsS).1)
          (mem_closure_of_mem <| Or.intro_left _ (hSA s hsS).2) (hSX s hsS)).1
            ((hAv.forall_map_apply_le_and_forall_apply_ne_zero_iff_exists_isIndex (hSA s hsS).1
              (hSA s hsS).2 (hSX s hsS)).2 ⟨F ⟨s, hsS⟩, G ⟨s, hsS⟩⟩)

open Classical in
lemma exists_isIndex_of_forall_exist_eq_and_mem_and_mem_and_forall_imp_and_exists_isIndex
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) {F : Finset (Π x : X, i x)}
    (h : ∀ f ∈ F, ∃ a b, f = a / b ∧ a ∈ A ∧ b ∈ A ∧ (∀ x : X, b x = 0 → a x = 0) ∧
      (∃ hAf : SpringLike' (closure (A.carrier.insert f)), hAf.isIndex v)) :
    ∃ hAF : SpringLike' (closure (A.carrier ∪ F.toSet)), hAF.isIndex v := by
  choose! a b hFab hFAa hFAb hFXba hFAv using h
  let S : Finset ((Π x : X, i x) × (Π x : X, i x)) := F.image (fun f => (a f, b f))
  have hSA : ∀ s ∈ S, s.1 ∈ A ∧ s.2 ∈ A := by
    intro s hsS
    obtain ⟨f, hfF, habfs⟩ := Finset.mem_image.1 hsS
    exact habfs ▸ ⟨hFAa f hfF, hFAb f hfF⟩
  have hSX : ∀ s ∈ S, ∀ x : X, s.2 x = 0 → s.1 x = 0 := by
    intro s hsS x hsx
    obtain ⟨f, hfF, habfs⟩ := Finset.mem_image.1 hsS
    have : b f x = s.2 x := habfs ▸ rfl
    have : a f x = 0 := hFXba f hfF x (this ▸ hsx)
    exact habfs ▸ this
  let G : Π s : S, SpringLike' (closure (A.carrier.insert (s.1.1 / s.1.2))) := by
    intro s
    obtain ⟨f, hfF, habfs⟩ := Finset.mem_image.1 s.2
    refine habfs ▸ ((hFab f hfF) ▸ hFAv f hfF).choose
  let H : Π s : S, (G s).isIndex v := by
    intro s
    obtain ⟨f, hfF, habfs⟩ := Finset.mem_image.1 s.2
    have : (G s).isIndex v = (hFab f hfF ▸ hFAv f hfF).choose.isIndex v := by
      congr
      · exact habfs ▸ rfl
      · exact habfs ▸ rfl
    exact this ▸ ((hFab f hfF) ▸ hFAv f hfF).choose_spec
  have : F.toSet = { s.1 / s.2 | s ∈ S } := by
    ext f
    refine ⟨fun hfF => ?_, fun ⟨s, hsS, hsf⟩ => ?_⟩
    · exact ⟨(a f, b f), Finset.mem_image_of_mem (fun f => (a f, b f)) hfF, (hFab f hfF).symm⟩
    · obtain ⟨f, hfF, habfs⟩ := Finset.mem_image.1 hsS
      exact hsf ▸ habfs ▸ (hFab f hfF) ▸ hfF
  exact this ▸ exists_isIndex_of_forall_springLike'_closure_insert_div_of_forall_isIndex
    hAv hSA hSX H

end SpringLike'.isIndex

open Classical in
lemma Subring.exists_finset_subset_and_mem_closure_union_of_mem_closure_union {R : Type*}
    [Ring R] {r : R} {A : Subring R} {S : Set R} (hrAS : r ∈ closure (A.carrier ∪ S)) :
    ∃ F : Finset R, F.toSet ⊆ S ∧ r ∈ Subring.closure (A.carrier ∪ F) := by
  refine closure_induction (fun a haAS => ?_) ?_ ?_ ?_ (fun a haAS ⟨F, hFS, haAF⟩ => ?_) ?_ hrAS
  · exact ⟨((Set.finite_singleton a).inter_of_left S).toFinset,
      fun b hbaS => Set.mem_of_mem_inter_right <|
        ((Set.finite_singleton a).inter_of_left S).mem_toFinset.1 hbaS,
      mem_closure_of_mem <| Or.elim haAS (fun hbB => Set.mem_union_left _ hbB)
        (fun haS => Set.mem_union_right _
          (((Set.finite_singleton a).inter_of_left S).mem_toFinset.2 <| Set.mem_inter rfl haS))⟩
  · exact ⟨∅, Finset.coe_empty ▸ ⟨Set.empty_subset S, zero_mem (closure (A.carrier ∪ ∅))⟩⟩
  · exact ⟨∅, Finset.coe_empty ▸ ⟨Set.empty_subset S, one_mem (closure (A.carrier ∪ ∅))⟩⟩
  · intro a b haAS hbAS ⟨F1, hF1S, haAF1⟩ ⟨F2, hF2S, hbAF2⟩
    refine ⟨F1 ∪ F2, F1.coe_union F2 ▸ Set.union_subset hF1S hF2S, Subring.add_mem _ ?_ ?_⟩
    · exact F1.coe_union F2 ▸ closure_mono (Set.union_assoc .. ▸ Set.subset_union_left) haAF1
    · exact F1.coe_union F2 ▸ closure_mono (Set.union_comm F1.toSet F2.toSet ▸ Set.union_assoc .. ▸
        Set.subset_union_left) hbAF2
  · exact ⟨F, hFS, Subring.neg_mem (closure (A.carrier ∪ F.toSet)) haAF⟩
  · intro a b haAS hbAS ⟨F1, hF1S, haAF1⟩ ⟨F2, hF2S, hbAF2⟩
    refine ⟨F1 ∪ F2, F1.coe_union F2 ▸ Set.union_subset hF1S hF2S, Subring.mul_mem _ ?_ ?_⟩
    · exact F1.coe_union F2 ▸ closure_mono (Set.union_assoc .. ▸ Set.subset_union_left) haAF1
    · exact F1.coe_union F2 ▸ closure_mono (Set.union_comm F1.toSet F2.toSet ▸ Set.union_assoc .. ▸
        Set.subset_union_left) hbAF2

lemma SpringLike'.isIndex.exists_springLike'_closure_union_isIndex
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) :
    ∃ h : SpringLike' (closure (A.carrier ∪
      { c : Π x : X, i x | ∃ a b, c = a / b ∧ a ∈ A ∧ b ∈ A ∧ (∀ x : X, b x = 0 → a x = 0) ∧
        ∃ hAc : SpringLike' (closure (A.carrier.insert c)), hAc.isIndex v })),
          h.isIndex v := by
  choose hXA1 hXA2 hXA3 using @exists_finset_subset_and_mem_closure_union_of_mem_closure_union
    (Π x : X, i x) _ (A := A) (S := { c : Π x : X, i x | ∃ a b, c = a / b ∧ a ∈ A ∧ b ∈ A ∧
      (∀ x : X, b x = 0 → a x = 0) ∧ (∃ hAc : SpringLike' (closure (A.carrier.insert c)),
        hAc.isIndex v) })
  choose hXA4 hXAv using
    @exists_isIndex_of_forall_exist_eq_and_mem_and_mem_and_forall_imp_and_exists_isIndex
      X _ i _ v A hA hAv
  use {
    spectralSpace := hA.spectralSpace
    forall_isOpen := fun c hcA => (hXA4 (fun f hfF => hXA2 c hcA hfF)).forall_isOpen c (hXA3 c hcA)
    forall_isCompact := fun c hcA =>
      (hXA4 (fun f hfF => hXA2 c hcA hfF)).forall_isCompact c (hXA3 c hcA)
    isTopologicalBasis := IsTopologicalBasis.of_isOpen_of_subset
      (fun U ⟨c, hcA, hcU⟩ => hcU ▸
        (hXA4 (fun f hfF => hXA2 c hcA hfF)).forall_isOpen c (hXA3 c hcA)) hA.isTopologicalBasis
      (fun U ⟨a, haA, haU⟩ => ⟨a, mem_closure_of_mem <| Or.intro_left _ haA, haU⟩) }
  exact {
    forall_isRankOneDiscrete := hAv.forall_isRankOneDiscrete
    exists_forall_eq := hAv.exists_forall_eq
    forall_le_of_ne := fun p a haA hap =>
      (hXAv (fun f hfF => hXA2 a haA hfF)).forall_le_of_ne p a (hXA3 a haA) hap
    forall_iff_of_ne := fun p a haA hap =>
      (hXAv (fun f hfF => hXA2 a haA hfF)).forall_iff_of_ne p a (hXA3 a haA) hap
    forall_exists_le := fun a haA =>
      (hXAv (fun f hfF => hXA2 a haA hfF)).forall_exists_le a (hXA3 a haA) }

def IndExtForV {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    (v : Π p : σ(X), Valuation (i p.z.1) NNRat) (A : Subring (Π x : X, i x)) :
    ℕ → Subring (Π x : X, i x)
  | 0 => A
  | n + 1 => closure ((IndExtForV v A n).carrier ∪
      { c : Π x : X, i x | ∃ a b, c = a / b ∧
        a ∈ IndExtForV v A n ∧ b ∈ IndExtForV v A n ∧ (∀ x : X, b x = 0 → a x = 0) ∧
        ∃ hAc : SpringLike' (closure ((IndExtForV v A n).carrier.insert c)), hAc.isIndex v })

lemma SpringLike'.isIndex.exists_springLike'_indExtForV_isIndex
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) (n : ℕ) :
    ∃ hAn : SpringLike' (IndExtForV v A n), hAn.isIndex v := by
  induction n with
  | zero => exact ⟨hA, hAv⟩
  | succ n hn =>
      obtain ⟨hAn, hAnv⟩ := hn
      exact hAnv.exists_springLike'_closure_union_isIndex

namespace IndExtForV

lemma subset_of_le {X : Type*} [TopologicalSpace X] {i : X → Type*}
    [(x : X) → Field (i x)] (v : Π p : σ(X), Valuation (i p.z.1) NNRat)
    (A : Subring (Π x : X, i x)) {m n : ℕ} (hmn : m ≤ n) :
    (IndExtForV v A m).carrier ⊆ (IndExtForV v A n).carrier :=
  Nat.le_induction (subset_of_eq rfl) (fun _ _ hAmnv =>
    hAmnv.trans <| subset_closure.trans <| closure_mono Set.subset_union_left) n hmn

lemma mono_of_isIndex_of_isIndex {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] (v : Π p : σ(X), Valuation (i p.z.1) NNRat)
    {A B : Subring (Π x : X, i x)} {hA : SpringLike' A} {hB : SpringLike' B}
    (hAB : A.carrier ⊆ B.carrier) (hAv : hA.isIndex v) (hBv : hB.isIndex v) (n : ℕ) :
    (IndExtForV v A n).carrier ⊆ (IndExtForV v B n).carrier := by
  induction n with
  | zero => exact hAB
  | succ n hn =>
      refine closure_mono <| Set.union_subset_union hn ?_
      · intro c ⟨a, b, hcab, hAanv, hAbnv, hXba, hAabcnv⟩
        refine ⟨a, b, hcab, hn hAanv, hn hAbnv, hXba, ?_⟩
        · obtain ⟨hAn, hAnv⟩ := hAv.exists_springLike'_indExtForV_isIndex n
          obtain ⟨hBn, hBnv⟩ := hBv.exists_springLike'_indExtForV_isIndex n
          exact hcab ▸ (hAnv.exists_isIndex_iff_exists_isIndex_of_subset hn hBnv hAanv hAbnv hXba).1
            <| hcab ▸ hAabcnv

end IndExtForV

def ISupExtForV {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    (v : Π p : σ(X), Valuation (i p.z.1) NNRat) (A : Subring (Π x : X, i x)) :
    Subring (Π x : X, i x) :=
  iSup fun n => IndExtForV v A n

lemma ISupExtForV.eq_iUnion_indExtForV {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] (v : Π p : σ(X), Valuation (i p.z.1) NNRat)
    (A : Subring (Π x : X, i x)) :
    (ISupExtForV v A).carrier = ⋃ n, (IndExtForV v A n).carrier :=
  coe_iSup_of_directed fun m n =>
    ⟨max m n, IndExtForV.subset_of_le v A (le_max_left m n),
      IndExtForV.subset_of_le v A (le_max_right m n)⟩

lemma mem_iSupExtForV_iff {X : Type*} [TopologicalSpace X] {i : X → Type*}
    [(x : X) → Field (i x)] (v : Π p : σ(X), Valuation (i p.z.1) NNRat)
    (A : Subring (Π x : X, i x)) (r : Π x : X, i x) :
    r ∈ ISupExtForV v A ↔ ∃ n, r ∈ IndExtForV v A n :=
  mem_iSup_of_directed fun m n =>
    ⟨max m n, IndExtForV.subset_of_le v A (le_max_left m n),
      IndExtForV.subset_of_le v A (le_max_right m n)⟩

namespace SpringLike'.isIndex

lemma exists_springLike'_iSupExtForV_isIndex
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) :
    ∃ hA : SpringLike' (ISupExtForV v A), hA.isIndex v := by
  choose hAX hAXv using fun r => (mem_iSupExtForV_iff v A r).1
  choose hAn hAnv using hAv.exists_springLike'_indExtForV_isIndex
  use {
    spectralSpace := hA.spectralSpace
    forall_isOpen := fun r hrA => (hAn <| hAX r hrA).forall_isOpen r (hAXv r hrA)
    forall_isCompact := fun r hrA => (hAn <| hAX r hrA).forall_isCompact r (hAXv r hrA)
    isTopologicalBasis := IsTopologicalBasis.of_isOpen_of_subset
      (fun U ⟨r, hrA, hrU⟩ => hrU ▸ (hAn <| hAX r hrA).forall_isOpen r <| hAXv r hrA)
      hA.isTopologicalBasis (fun U ⟨r, hrA, hrU⟩ => ⟨r, (mem_iSupExtForV_iff v A r).2 ⟨0, hrA⟩, hrU⟩)
  }
  exact {
    forall_isRankOneDiscrete := hAv.forall_isRankOneDiscrete
    exists_forall_eq := hAv.exists_forall_eq
    forall_le_of_ne := fun p r hrA hrp => (hAnv <| hAX r hrA).forall_le_of_ne p r (hAXv r hrA) hrp
    forall_iff_of_ne := fun p r hrA hrp => (hAnv <| hAX r hrA).forall_iff_of_ne p r (hAXv r hrA) hrp
    forall_exists_le := fun r hrA => (hAnv <| hAX r hrA).forall_exists_le r <| hAXv r hrA }

def iSupExtForV {X : Type*} [TopologicalSpace X] {i : X → Type*}
    [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (hAv : hA.isIndex v) :
    SpringLike' (ISupExtForV v A) :=
  hAv.exists_springLike'_iSupExtForV_isIndex.choose

lemma iSupExtForV_isIndex {X : Type*} [TopologicalSpace X] {i : X → Type*}
    [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (hAv : hA.isIndex v) :
    hAv.iSupExtForV.isIndex v :=
  hAv.exists_springLike'_iSupExtForV_isIndex.choose_spec

/-- This is Proposition 1 in the paper. -/
lemma mem_radical_span_singleton_of_forall_imp {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (hAv : hA.isIndex v)
    {a b : ISupExtForV v A} (hXab : ∀ x : X, b.1 x = 0 → a.1 x = 0) :
    a ∈ (Ideal.span {b}).radical := by
  obtain ⟨m, hAamv⟩ := (mem_iSupExtForV_iff v A a.1).1 a.2
  obtain ⟨n, hAbnv⟩ := (mem_iSupExtForV_iff v A b.1).1 b.2
  have hAamnv : a.1 ∈ IndExtForV v A (max m n) :=
    IndExtForV.subset_of_le v A (le_max_left m n) hAamv
  have hAbmnv : b.1 ∈ IndExtForV v A (max m n) :=
    IndExtForV.subset_of_le v A (le_max_right m n) hAbnv
  obtain ⟨hAmn, hAmnv⟩ := hAv.exists_springLike'_indExtForV_isIndex (max m n)
  obtain ⟨q, hq, hXbqv⟩ := hAmnv.forall_exists_le b.1 hAbmnv
  obtain ⟨N, hN, hNXaqv⟩ :
      ∃ N > 0, ∀ p : σ(X), a.1 p.z.1 ≠ 0 → v p (a.1 p.z.1) ≠ 1 → v p ((a.1 ^ N) p.z.1) < q := by
    by_cases hσX : Nonempty σ(X)
    · simp only [Pi.pow_apply, map_pow]
      let s : NNRatˣ := ⟨q, q⁻¹, mul_inv_cancel₀ (ne_of_lt hq).symm,
        inv_mul_cancel₀ (ne_of_lt hq).symm⟩
      obtain ⟨N, hNs⟩ := exists_pow_lt (hAmnv.choose_lt_one <| Classical.choice hσX) s
      refine ⟨N + 1, N.zero_lt_succ, fun p hap hvpa => ?_⟩
      · have : v p (a.1 p.z.1) ^ N < q := lt_of_le_of_lt
          (pow_le_pow_left' (hAmnv.map_apply_le_choose_of_apply_ne_zero_of_map_apply_ne_one
            hAamnv hap hvpa) N)
          (hAmnv.exists_forall_eq.choose.val_pow_eq_pow_val N ▸ Units.val_lt_val.2 hNs)
        exact lt_of_le_of_lt (pow_add (v p _) N 1 ▸ mul_le_of_le_one_right (zero_le _)
          ((pow_one (v p _)).symm ▸ hAmnv.forall_le_of_ne p a.1 hAamnv hap)) this
    · exact ⟨1, Nat.one_pos, fun p => ((not_nonempty_iff.1 hσX).1 p).elim⟩
  have hANabmnv : ∃ hANabmn :
      SpringLike' (closure ((IndExtForV v A (max m n)).carrier.insert (a.1 ^ N / b.1))),
        hANabmn.isIndex v := by
    refine (hAmnv.forall_map_apply_le_and_forall_apply_ne_zero_iff_exists_isIndex
      ((IndExtForV v A (max m n)).pow_mem hAamnv N) hAbmnv
      (fun x hbx => Pi.pow_apply a.1 N x ▸ (hXab x hbx).symm ▸
        (zero_pow_eq_zero.2 <| Nat.ne_zero_of_lt hN))).1 (fun p hNap => ?_)
    · have hap : a.1 p.z.1 ≠ 0 := fun hap =>
        (hap ▸ Pi.pow_apply a.1 N p.z.1 ▸ hNap) (zero_pow_eq_zero.2 <| Nat.ne_zero_of_lt hN)
      have hbp : b.1 p.z.1 ≠ 0 := fun h => hap <| hXab p.z.1 h
      refine ⟨?_, fun hNabpv hbp => not_lt_of_ge (hXbqv p (fun hbp => hap <| hXab p.z.1 hbp))
        (hNabpv ▸ hNXaqv p hap <| imp_not_comm.1 (hAmnv.forall_iff_of_ne p a hAamnv hap).1
          (hXab p.z.2 hbp))⟩
      · by_cases hvpa : v p (a.1 p.z.1) = 1
        · have hvpb : v p (b.1 p.z.1) = 1 := (hAmnv.forall_iff_of_ne p b hAbmnv hbp).2 <|
            (not_imp_not.2 <| hXab p.z.2) ((hAmnv.forall_iff_of_ne p a hAamnv hap).1 hvpa)
          exact Pi.pow_apply a.1 N p.z.1 ▸ (v p).map_pow .. ▸ hvpa ▸ hvpb.symm ▸
            (one_pow (M := NNRat) N).symm ▸ le_rfl
        · exact le_of_lt <| lt_of_lt_of_le (hNXaqv p hap hvpa) (hXbqv p hbp)
  have hANabv : a.1 ^ N / b.1 ∈ ISupExtForV v A :=
    (mem_iSupExtForV_iff v A (a.1 ^ N / b.1)).2
      ⟨max m n + 1, mem_closure_of_mem <| Or.intro_right _
        ⟨a.1 ^ N, b.1, rfl, (IndExtForV v A (max m n)).pow_mem hAamnv N, hAbmnv, fun x hbx =>
          Pi.pow_apply a.1 N x ▸ (hXab x hbx).symm ▸ (zero_pow_eq_zero.mpr <| Nat.ne_zero_of_lt hN),
            hANabmnv⟩⟩
  exact ⟨N, Ideal.mem_span_singleton'.mpr ⟨⟨a.1 ^ N / b.1, hANabv⟩,
    SetLike.coe_eq_coe.mp <| Pi.div_mul_cancel_of_forall_imp (f := a.1 ^ N) (fun x hbx =>
      Pi.pow_apply a.1 N x ▸ (hXab x hbx).symm ▸ (zero_pow_eq_zero.mpr <| Nat.ne_zero_of_lt hN))⟩⟩

end SpringLike'.isIndex

end ProvingThm3AndProp1
