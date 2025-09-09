import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic

import Hochster.Section3

open CommRing ConstructibleTop Polynomial SpringLike' Subring TopologicalSpace Topology Valuation

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
    {p : σ(X)} (hap : a p.z.1 ≠ 0) {hAab : SpringLike' (closure (A.carrier.insert (a / b)))}
    (hAabv : hAab.isIndex v) : v p (a p.z.1) ≤ v p (b p.z.1) := by
  refine Pi.div_mul_cancel_of_forall_imp hab ▸ p.map_mul_apply_of_pi_valuation v _ b ▸
    (mul_le_iff_le_one_left ?_).2 ?_
  · exact (v p).pos_iff.2 fun hbp => hap (hab p.z.1 hbp)
  · refine hAabv.forall_le_of_ne p (a / b) ?_ (fun habp => ?_)
    · exact mem_closure_of_mem <| A.carrier.mem_insert (a / b)
    · exact Or.elim (div_eq_zero_iff.mp habp) hap (fun hbp => hap (hab p.z.1 hbp))

lemma ne_zero_of_pi_valuation_of_v_extension_of_map_apply_eq {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → Field (i x)] {v : Π p : σ(X), Valuation (i p.z.1) NNRat}
    {A : Subring (Π x : X, i x)} {a b : Π x : X, i x} (hab : ∀ x : X, b x = 0 → a x = 0)
    {p : σ(X)} (hap : a p.z.1 ≠ 0) {hAab : SpringLike' (closure (A.carrier.insert (a / b)))}
    (hAabv : hAab.isIndex v) (hvpab : v p (a p.z.1) = v p (b p.z.1)) :
    a p.z.2 ≠ 0 := by
  intro h
  have h1 : (a / b) p.z.2 = 0 := Pi.div_apply a b p.z.2 ▸ h ▸ zero_div (b p.z.2)
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

lemma SpringLike'.isClosed_vanishing_set_of_forall_map_apply_le_of_forall_ne_zero
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {v : Π p : σ(X), Valuation (i p.z.1) NNRat} {A : Subring (Π x : X, i x)}
    {hA : SpringLike' A} (hAv : hA.isIndex v) {a b r : Π x : X, i x} (ha : a ∈ A) (hb : b ∈ A)
    (hab : ∀ x : X, b x = 0 → a x = 0) (hr : r ∈ closure (A.carrier.insert (a / b)))
    (h1 : ∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) ≤ v p (b p.z.1))
    (h2 : ∀ p : σ(X), a p.z.1 ≠ 0 → v p (a p.z.1) = v p (b p.z.1) → a p.z.2 ≠ 0) :
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
        have hvpab := lt_of_le_of_ne (h1 p hay) (imp_not_comm.1 (h2 p hay) (hab x hbx))
        have habry : -((repPoly hr).coeff 0 y * b y ^ (repPoly hr).natDegree) =
            ∑ n ∈ Finset.range ((repPoly hr).natDegree + 1) \ {0},
              (repPoly hr).coeff n y * a y ^ n * b y ^ ((repPoly hr).natDegree - n) := by
          have := mul_eq_zero_of_left ((Finset.sum_sdiff (f := fun n => (repPoly hr).coeff .. * _)
            <| Finset.singleton_subset_iff.mpr <| Finset.mem_range.mpr <| (1 : ℕ).le_add_left _) ▸
            Pi.polynomial_eval_apply' (repPoly hr) _ y ▸ Set.mem_setOf_eq ▸ repPoly_eval_eq hr ▸
              hry) (b y ^ (repPoly hr).natDegree)
          simp only [add_mul, add_eq_zero_iff_neg_eq', Finset.sum_singleton, pow_zero, mul_one,
            Finset.sum_mul] at this
          exact this ▸ Finset.sum_congr rfl fun n hn => mul_assoc ((repPoly hr).coeff ..) .. ▸
            (mul_assoc ((repPoly hr).coeff ..) ..).symm ▸ (Nat.add_sub_of_le <|
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
