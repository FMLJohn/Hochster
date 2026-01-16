import Hochster.Section5

import Mathlib.Algebra.MvPolynomial.Basic

open CategoryTheory Finset Function IsFractionRing MvPolynomial Subring OreLocalization
  TopologicalSpace Valuation

/-- The category of spaces with indeterminates. -/
@[ext]
structure SWICat where
  X : Type*
  tX : TopologicalSpace X
  spectralSpace : SpectralSpace X
  E : Type*
  g : E → Set X
  forall_isCompact (e : E) : IsCompact (g e)
  forall_isOpen (e : E) : IsOpen (g e)
  eq_generateFrom : tX = generateFrom (Set.range g)

attribute [instance] SWICat.tX SWICat.spectralSpace

namespace SWICat

structure Hom (I J : SWICat) where
  f : I.X → J.X
  isSpectralMap : IsSpectralMap f
  r : J.E → I.E
  injective : Function.Injective r
  comp_eq_comp : I.g ∘ r = (fun o => f ⁻¹' o) ∘ J.g

def Hom.id (I : SWICat) : Hom I I where
  f := fun x => x
  isSpectralMap := isSpectralMap_id
  r := fun e => e
  injective := injective_id
  comp_eq_comp := by ext; simp

def Hom.comp {I J K : SWICat} (hom1 : I.Hom J) (hom2 : J.Hom K) : I.Hom K where
  f := hom2.f ∘ hom1.f
  isSpectralMap := hom2.isSpectralMap.comp hom1.isSpectralMap
  r := hom1.r ∘ hom2.r
  injective := hom1.injective.comp hom2.injective
  comp_eq_comp := funext fun e => comp_apply (g := K.g) ▸ Set.preimage_comp.symm ▸
    (comp_apply (g := K.g) ▸ funext_iff.1 hom2.comp_eq_comp e) ▸ comp_assoc .. ▸ comp_apply ▸
    comp_apply (f := J.g) ▸ funext_iff.1 hom1.comp_eq_comp (hom2.r e)

instance : Category SWICat where
  Hom I J := Hom I J
  id I := Hom.id I
  comp hom1 hom2 := hom1.comp hom2
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end SWICat

namespace Subring

theorem exists_mvPolynomial_of_mem_closure' {R : Type*} [CommRing R]
    {A : Subring R} {S : Set R} {r : R} (hr : r ∈ closure (A.carrier ∪ S)) :
    ∃ p : MvPolynomial S A, (p.map A.subtype).eval (fun s : S => s.1) = r := by
  refine closure_induction (fun r hr => ?_) ⟨0, rfl⟩ ?_ (fun r s _ _ ⟨p, hpr⟩ ⟨q, hqs⟩ => ?_)
    (fun r _ ⟨p, hpr⟩ => ?_) (fun r s _ _ ⟨p, hpr⟩ ⟨q, hqs⟩ => ?_) hr
  · refine hr.elim (fun hr => ?_) (fun hr => ?_)
    · exact ⟨C ⟨r, hr⟩, map_C A.subtype _ ▸ A.subtype_apply _ ▸ eval_C r⟩
    · exact ⟨X ⟨r, hr⟩, map_X A.subtype _ ▸ eval_X (f := fun s : S => s.1) _ ▸ rfl⟩
  · exact ⟨1, map_one (MvPolynomial.map A.subtype) ▸ map_one _⟩
  · exact ⟨p + q, map_add (MvPolynomial.map A.subtype) p q ▸ (p.map A.subtype).eval_add ▸
      hpr ▸ hqs ▸ rfl⟩
  · exact ⟨-p, map_neg (MvPolynomial.map A.subtype) p ▸ (p.map A.subtype).eval_neg .. ▸ hpr ▸ rfl⟩
  · exact ⟨p * q, map_mul (MvPolynomial.map A.subtype) p q ▸ (p.map A.subtype).eval_mul ▸
      hpr ▸ hqs ▸ rfl⟩

theorem exists_mvPolynomial_of_mem_closure {R : Type*} [CommRing R]
    {A : Subring R} {S : Set R} {r : R} (hr : r ∈ closure (A.carrier ∪ S)) :
    ∃ p : MvPolynomial S R, p.eval (fun s : S => s.1) = r ∧
      ∀ m : S →₀ ℕ, p.coeff m ∈ A := by
  obtain ⟨p, hp⟩ := exists_mvPolynomial_of_mem_closure' hr
  exact ⟨p.map A.subtype, hp, fun m => p.coeff_map A.subtype m ▸ A.subtype_apply _ ▸
    SetLike.coe_mem (coeff m p)⟩

/--
`Subring.repMvPoly hr = (Subring.exists_mvPolynomial_of_mem_closure hr).choose`.
-/
noncomputable def repMvPoly {R : Type*} [CommRing R] {A : Subring R}
    {S : Set R} {r : R} (hr : r ∈ closure (A.carrier ∪ S)) :=
  (exists_mvPolynomial_of_mem_closure hr).choose

lemma repMvPoly_eval_eq {R : Type*} [CommRing R] {A : Subring R}
    {S : Set R} {r : R} (hr : r ∈ closure (A.carrier ∪ S)) :
    (repMvPoly hr).eval (fun s : S => s.1) = r :=
  (exists_mvPolynomial_of_mem_closure hr).choose_spec.1

lemma coeff_repMvPoly_mem {R : Type*} [CommRing R] {A : Subring R}
    {S : Set R} {r : R} (hr : r ∈ closure (A.carrier ∪ S)) (m : S →₀ ℕ) :
    (repMvPoly hr).coeff m ∈ A :=
  (exists_mvPolynomial_of_mem_closure hr).choose_spec.2 m

lemma exists_mvPolynomial_of_le_range_of_mem_closure {A R : Type*}
    [CommRing A] [CommRing R] {r : R} {S : Set R} {B : Subring R}
    {h : A →+* R} (hBh : B ≤ h.range) (hBSr : r ∈ closure (B.carrier ∪ S)) :
    ∃ p : MvPolynomial S A, (p.map h).eval (fun s : S => s.1) = r := by
  refine closure_induction (fun r hr => ?_) ⟨0, rfl⟩ ?_ (fun r s _ _ ⟨p, hpr⟩ ⟨q, hqs⟩ => ?_)
    (fun r _ ⟨p, hpr⟩ => ?_) (fun r s _ _ ⟨p, hpr⟩ ⟨q, hqs⟩ => ?_) hBSr
  · refine hr.elim (fun hBr => ?_) (fun hrS => ?_)
    · obtain ⟨a, har⟩ := hBh hBr
      exact ⟨C a, har ▸ (map_C h a).symm ▸ eval_C (h a)⟩
    · exact ⟨X ⟨r, hrS⟩, map_X h _ ▸ eval_X _⟩
  · exact ⟨1, map_one (MvPolynomial.map h) ▸ map_one _⟩
  · exact ⟨p + q, (MvPolynomial.map h).map_add p q ▸ eval_add (R := R) ▸ hqs ▸ hpr ▸ rfl⟩
  · exact ⟨-p, (MvPolynomial.map h).map_neg p ▸ eval_neg (R := R) .. ▸ hpr ▸ rfl⟩
  · exact ⟨p * q, (MvPolynomial.map h).map_mul p q ▸ eval_mul (R := R) ▸ hqs ▸ hpr ▸ rfl⟩

/--
`Subring.repMvPoly' hBh hBSr := (exists_mvPolynomial_of_le_range_of_mem_closure hBh hBSr).choose`.
-/
noncomputable def repMvPoly' {A R : Type*} [CommRing A] [CommRing R]
    {r : R} {S : Set R} {B : Subring R} {h : A →+* R} (hBh : B ≤ h.range)
    (hBSr : r ∈ closure (B.carrier ∪ S)) :=
  (exists_mvPolynomial_of_le_range_of_mem_closure hBh hBSr).choose

lemma map_repMvPoly'_eval_eq {A R : Type*} [CommRing A] [CommRing R]
    {r : R} {S : Set R} {B : Subring R} {h : A →+* R} (hBh : B ≤ h.range)
    (hBSr : r ∈ closure (B.carrier ∪ S)) :
    ((repMvPoly' hBh hBSr).map h).eval (fun s : S => s.1) = r :=
  (exists_mvPolynomial_of_le_range_of_mem_closure hBh hBSr).choose_spec

lemma exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure
    {A R σ : Type*} [CommRing A] [CommRing R] {r : R} {S : Set R} {B : Subring R}
    {h : A →+* R} (hBh : B ≤ h.range) {f : σ → R} (hSf : S ⊆ Set.range f)
    (hBSr : r ∈ closure (B.carrier ∪ S)) :
    ∃ p : MvPolynomial σ A, (p.map h).eval (fun s => f s) = r := by
  refine closure_induction (fun r hr => ?_) ⟨0, rfl⟩ ?_ (fun r s _ _ ⟨p, hpr⟩ ⟨q, hqs⟩ => ?_)
    (fun r _ ⟨p, hpr⟩ => ?_) (fun r s _ _ ⟨p, hpr⟩ ⟨q, hqs⟩ => ?_) hBSr
  · refine hr.elim (fun hBr => ?_) (fun hrS => ?_)
    · obtain ⟨a, har⟩ := hBh hBr
      exact ⟨C a, har ▸ map_C h a ▸ eval_C (h a)⟩
    · obtain ⟨s, _, _⟩ := hSf hrS
      exact ⟨X s, map_X h s ▸ eval_X s⟩
  · exact ⟨1, map_one (MvPolynomial.map h) ▸ map_one _⟩
  · exact ⟨p + q, (MvPolynomial.map h).map_add p q ▸ eval_add (R := R) ▸ hqs ▸ hpr ▸ rfl⟩
  · exact ⟨-p, (MvPolynomial.map h).map_neg p ▸ eval_neg (R := R) .. ▸ hpr ▸ rfl⟩
  · exact ⟨p * q, (MvPolynomial.map h).map_mul p q ▸ eval_mul (R := R) ▸ hqs ▸ hpr ▸ rfl⟩

/--
`Subring.repMvPoly'' hBh hSf hBSr` is defined as
`(exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure hBh hSf hBSr).choose`.
-/
noncomputable def repMvPoly''
    {A R σ : Type*} [CommRing A] [CommRing R] {r : R} {S : Set R} {B : Subring R}
    {h : A →+* R} (hBh : B ≤ h.range) {f : σ → R} (hSf : S ⊆ Set.range f)
    (hBSr : r ∈ closure (B.carrier ∪ S)) :=
  (exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure hBh hSf hBSr).choose

lemma map_repMvPoly''_eval_eq {A R σ : Type*} [CommRing A] [CommRing R] {r : R} {S : Set R}
    {B : Subring R} {h : A →+* R} (hBh : B ≤ h.range) {f : σ → R} (hSf : S ⊆ Set.range f)
    (hBSr : r ∈ closure (B.carrier ∪ S)) :
    ((repMvPoly'' hBh hSf hBSr).map h).eval (fun s => f s) = r :=
  (exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure hBh hSf hBSr).choose_spec

end Subring

namespace SWICat

open Classical in
noncomputable def T (k : Type*) [Field k] {I : SWICat} (e : I.E) :
    I.X → MvPolynomial I.E k :=
  fun x => if x ∈ I.g e then MvPolynomial.X e else 0

lemma T_apply_eq_zero_iff (k : Type*) [Field k] {I : SWICat}
    (x : I.X) (e : I.E) : T k e x = 0 ↔ x ∉ I.g e := by
  simp [T]

lemma T_apply_ne_zero_iff (k : Type*) [Field k] {I : SWICat}
    (x : I.X) (e : I.E) : T k e x ≠ 0 ↔ x ∈ I.g e := by
  simp [T]

lemma finite_image_T (k : Type*) [Field k] {I : SWICat} (e : I.E) :
    { T k e x | x : I.X }.Finite := by
  refine ((Set.finite_singleton 0).insert (MvPolynomial.X e)).subset fun p ⟨x, hpx⟩ => ?_
  · by_cases hex : x ∈ I.g e
    · simp only [← hpx, T, hex, reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff, X_ne_zero,
        or_false]
    · simp only [← hpx, T, hex, reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]

lemma T_support_eq_g (k : Type*) [Field k] {I : SWICat} (e : I.E) :
    { x : I.X | T k e x ≠ 0 } = I.g e := by
  simp [T]

lemma T_mul_T_support_eq_inter (k : Type*) [Field k] {I : SWICat} (d e : I.E) :
    { x : I.X | (T k d * T k e) x ≠ 0 } =
      { x : I.X | T k d x ≠ 0 } ∩ { x : I.X | T k e x ≠ 0 } := by
  simp only [Pi.mul_apply, T, mul_ite, ite_mul, zero_mul, mul_zero, ne_eq, ite_eq_right_iff,
    mul_eq_zero, X_ne_zero, or_self, imp_false, Classical.not_imp, not_not, Set.sep_mem_eq,
    Set.setOf_mem_eq, Set.inter_comm]

lemma prod_T_support_eq_biInter (k : Type*) [Field k]
    {I : SWICat} {ι : Type*} (s : Finset ι) (f : ι → I.E) :
    { x : I.X | (∏ i ∈ s, T k (f i)) x ≠ 0 } = ⋂ i ∈ s, I.g (f i) := by
  ext x
  simp only [s.prod_apply, Set.mem_iInter]
  exact s.prod_ne_zero_iff.trans ⟨fun h i his => (T_apply_ne_zero_iff k x (f i)).1 (h i his),
    fun h i his => (T_apply_ne_zero_iff k x (f i)).2 (h i his)⟩

-- lemma eval_map_ringHom_apply_eq_eval_map_C_apply {k : Type*} [Field k]
--     {I : SWICat} (x : I.X) (p : MvPolynomial { T k e | e : I.E } k) :
--     (p.map (Pi.ringHom fun _ => C)).eval (fun s => s.1) x =
--     (p.map C).eval fun s => s.1 x := by
--   refine @p.induction_on k _ _ (fun p => (p.map (Pi.ringHom fun x => C)).eval _ x =
--     (p.map C).eval _) (fun i => ?_) (fun p q => ?_) (fun p T => ?_)
--   · simp only [map_C, eval_C, Pi.ringHom_apply]
--   · simp only [map_add]
--     exact fun hp hq => hp ▸ hq ▸ rfl
--   · simp only [map_mul, map_X, eval_X]
--     exact fun hp => hp ▸ rfl

lemma eval_map_ringHom_apply_eq_eval_map_C_apply' {k : Type*} [Field k]
    {I : SWICat} (x : I.X) (p : MvPolynomial I.E k) :
    (p.map (Pi.ringHom fun _ => C)).eval (T k) x = (p.map C).eval fun e => T k e x := by
  refine @p.induction_on k _ _ (fun p => (p.map (Pi.ringHom fun x => C)).eval _ x =
    (p.map C).eval _) (fun i => ?_) (fun p q => ?_) (fun p _ => ?_)
  · simp only [map_C, eval_C, Pi.ringHom_apply]
  · simp only [map_add]
    exact fun hp hq => hp ▸ hq ▸ rfl
  · simp only [map_mul, map_X, eval_X]
    exact fun hp => hp ▸ rfl

/--
`SWICat.evalMapApplyPoly x p := (p.map (Pi.ringHom fun _ => C)).eval (T k) x`.
-/
noncomputable def evalMapApplyPoly {k : Type*} [Field k] {I : SWICat}
    (x : I.X) (p : MvPolynomial I.E k) :=
  (p.map (Pi.ringHom fun _ => C)).eval (T k) x

lemma evalMapApplyPoly_def {k : Type*} [Field k] {I : SWICat}
    (x : I.X) (p : MvPolynomial I.E k) :
  evalMapApplyPoly x p = (p.map (Pi.ringHom fun _ => C)).eval (T k) x := rfl

lemma evalMapApplyPoly_zero (k : Type*) [Field k] {I : SWICat} (x : I.X) :
    evalMapApplyPoly (k := k) x 0 = 0 := by
  simp [evalMapApplyPoly]

lemma evalMapApplyPoly_one (k : Type*) [Field k] {I : SWICat} (x : I.X) :
    evalMapApplyPoly (k := k) x 1 = 1 := by
  simp [evalMapApplyPoly]

lemma evalMapApplyPoly_C {k : Type*} [Field k] (i : k)
    {I : SWICat} (x : I.X) :
    evalMapApplyPoly x (C i) = C i := by
  simp [evalMapApplyPoly]

lemma evalMapApplyPoly_X (k : Type*) [Field k] {I : SWICat} (x : I.X) (e : I.E) :
    evalMapApplyPoly (k := k) x (MvPolynomial.X e) = T k e x := by
  simp [evalMapApplyPoly]

lemma evalMapApplyPoly_add {k : Type*} [Field k] {I : SWICat}
    (x : I.X) (p q : MvPolynomial I.E k) :
    evalMapApplyPoly x (p + q) = evalMapApplyPoly x p + evalMapApplyPoly x q := by
  simp [evalMapApplyPoly]

lemma evalMapApplyPoly_mul {k : Type*} [Field k] {I : SWICat}
    (x : I.X) (p q : MvPolynomial I.E k) :
    evalMapApplyPoly x (p * q) = evalMapApplyPoly x p * evalMapApplyPoly x q := by
  simp [evalMapApplyPoly]

lemma evalMapApplyPoly_sum {k : Type*} [Field k] {I : SWICat} (x : I.X)
    {ι : Type u_1} (s : Finset ι) (f : ι → MvPolynomial I.E k) :
    evalMapApplyPoly x (s.sum f) = s.sum fun i => evalMapApplyPoly x (f i) := by
  simp [evalMapApplyPoly]

lemma evalMapApplyPoly_prod {k ι : Type*} [Field k] {I : SWICat} (x : I.X)
    (s : Finset ι) (f : ι → MvPolynomial I.E k) :
    evalMapApplyPoly x (s.prod f) = s.prod fun i => evalMapApplyPoly x (f i) := by
  simp [evalMapApplyPoly]

open Classical in
lemma evalMapApplyPoly_monomial {k : Type*} [Field k]
    (i : k) {I : SWICat} (x : I.X) (m : I.E →₀ ℕ) :
    evalMapApplyPoly x (monomial m i) =
    if ∃ e ∈ m.support, x ∉ I.g e then 0 else monomial m i := by
  haveI : Nonempty I.X := ⟨x⟩
  simp only [evalMapApplyPoly, eval_eq, map_monomial, coeff_monomial, support_monomial]
  by_cases hmx : ∃ e ∈ m.support, x ∉ I.g e
  · simp only [hmx, reduceIte]
    by_cases hi : (Pi.ringHom fun x : I.X => @C k I.E _) i = 0
    · simp only [hi, zero_mul, ite_self, Pi.zero_apply, sum_const_zero]
    · simp only [hi, reduceIte, sum_singleton, Pi.mul_apply, prod_apply]
      obtain ⟨e, hem, he⟩ := hmx
      refine mul_eq_zero.2 <| Or.intro_right _ <| prod_eq_zero hem ?_
      · simp only [Pi.pow_apply, T, he, reduceIte, ne_eq, Finsupp.mem_support_iff.1 hem,
          not_false_eq_true, zero_pow]
  · simp only [hmx]
    by_cases hi : (Pi.ringHom fun x : I.X => @C k I.E _) i = 0
    · simp only [hi]
      exact ((RingHom.ker_eq_bot_iff_eq_zero _).1 <| (RingHom.injective_iff_ker_eq_bot _).1 <|
        Pi.ringHom_injective _ (fun _ => C_injective I.E k)) i hi ▸ monomial_zero.symm
    · simp only [hi, reduceIte, sum_singleton, Pi.mul_apply, prod_apply, Pi.pow_apply]
      refine monomial_eq (a := i) (s := m) ▸
        (mul_eq_mul_left_iff.2 <| Or.intro_left _ <| prod_congr rfl fun e hem => ?_)
      · simp only [not_exists, not_and, not_not] at hmx
        simp only [T, hmx e hem, reduceIte]

open Classical in
lemma coeff_evalMapApplyPoly {k : Type*} [Field k] {I : SWICat}
    (x : I.X) (m : I.E →₀ ℕ) (p : MvPolynomial I.E k) :
    (evalMapApplyPoly x p).coeff m =
    if ∃ e ∈ m.support, x ∉ I.g e then 0 else p.coeff m := by
  refine p.monomial_add_induction_on (fun i => ?_) (fun n i p hnp hi hmp => ?_)
  · simp only [evalMapApplyPoly, map_C, eval_C, Pi.ringHom_apply, coeff_C]
    by_cases hmx : ∃ e ∈ m.support, x ∉ I.g e
    · simp only [hmx, reduceIte, ite_eq_right_iff]
      obtain ⟨e, hem, he⟩ := hmx
      exact fun hm => ((List.mem_nil_iff e).mp (hm ▸ hem : e ∈ Finsupp.support 0)).elim
    · simp only [hmx, reduceIte]
  · simp only [evalMapApplyPoly_add, coeff_add] at hmp ⊢
    by_cases hmx : ∃ e ∈ m.support, x ∉ I.g e
    · simp only [hmx, hmp, reduceIte, add_zero, evalMapApplyPoly_monomial i x n]
      · by_cases hmn : n = m
        · simp only [hmn, hmx, reduceIte, coeff_zero]
        · by_cases hnx : ∃ e ∈ n.support, x ∉ I.g e
          · simp only [hnx, reduceIte, coeff_zero]
          · simp only [hnx, reduceIte, coeff_monomial m n i, hmn]
    · simp only [hmx, coeff_monomial] at hmp ⊢
      refine hmp.symm ▸ (add_left_inj (coeff m p)).mpr ?_
      · by_cases hmn : n = m
        · refine hmn.symm ▸ evalMapApplyPoly_monomial i x m ▸ ?_
          · simp only [hmx, reduceIte, coeff_monomial]
        · simp only [evalMapApplyPoly_monomial i x n, hmn]
          · by_cases hnx : ∃ e ∈ n.support, x ∉ I.g e
            · simp only [hnx, reduceIte, coeff_zero]
            · simp only [hnx, reduceIte, coeff_monomial m n i, hmn]

lemma support_evalMapApplyPoly {k : Type*} [Field k]
    {I : SWICat} (x : I.X) (p : MvPolynomial I.E k) :
    (evalMapApplyPoly x p).support =
      { m : I.E →₀ ℕ | m ∈ p.support ∧ ∀ e ∈ m.support, x ∈ I.g e } := by
  ext m
  refine mem_support_iff.trans <| ⟨fun hmpx => ?_, fun ⟨hmp, hmx⟩ => ?_⟩
  · have := coeff_evalMapApplyPoly x m p ▸ hmpx
    simp only [ne_eq, ite_eq_left_iff, Classical.not_imp, not_exists, not_and, not_not] at this
    exact ⟨mem_support_iff.2 this.2, this.1⟩
  · have hmpx := coeff_evalMapApplyPoly x m p
    have : ¬∃ e ∈ m.support, x ∉ I.g e := by
      simpa only [not_exists, not_and, not_not] using hmx
    simp only [this] at hmpx
    exact hmpx ▸ mem_support_iff.1 hmp

lemma support_evalMapApplyPoly_subset {k : Type*} [Field k]
    {I : SWICat} (x : I.X) (p : MvPolynomial I.E k) :
    (evalMapApplyPoly x p).support ⊆ p.support :=
  fun _ hpx => (support_evalMapApplyPoly x p ▸ mem_coe.2 hpx).1

lemma finite_evalMapApplyPoly_image {k : Type*} [Field k]
    {I : SWICat} (p : MvPolynomial I.E k) :
    { evalMapApplyPoly x p | x : I.X }.Finite := by
  refine @induction_on k I.E _ (fun p => { evalMapApplyPoly x p | x : I.X }.Finite) p
    (fun i => ?_) (fun p q => ?_) (fun p e hp => ?_)
  · simp only [evalMapApplyPoly_C]
    exact (Set.finite_singleton (C i)).subset fun a ⟨_, ha⟩ => ha ▸ rfl
  · simp only [evalMapApplyPoly_add]
    exact fun hp hq => (hp.add hq).subset fun _ ⟨x, hpq⟩ =>
      ⟨evalMapApplyPoly x p, ⟨x, rfl⟩, evalMapApplyPoly x q, ⟨x, rfl⟩, hpq⟩
  · simp only [evalMapApplyPoly_mul, evalMapApplyPoly_X]
    exact (hp.mul (finite_image_T k e)).subset fun _ ⟨x, hpx⟩ =>
      hpx ▸ ⟨evalMapApplyPoly x p, ⟨x, rfl⟩, T k e x, ⟨x, rfl⟩, rfl⟩

lemma evalMapApplyPoly_monomial_support_eq_biInter (k : Type*) [Field k]
    {i : k} (hi : i ≠ 0) {I : SWICat} (m : I.E →₀ ℕ) :
    { x : I.X | evalMapApplyPoly x (monomial m i) ≠ 0 } = ⋂ e ∈ m.support, I.g e := by
  ext x
  simp [evalMapApplyPoly_monomial, hi]

open Classical in
lemma evalMapApplyPoly_support_eq_biUnion {k : Type*} [Field k]
    {i : k} (hi : i ≠ 0) {I : SWICat} (p : MvPolynomial I.E k) :
    { x : I.X | evalMapApplyPoly x p ≠ 0 } =
      ⋃ m ∈ p.support, { x : I.X | evalMapApplyPoly x (monomial m i) ≠ 0 } := by
  ext x
  simp only [Set.mem_setOf_eq, (evalMapApplyPoly x p).ne_zero_iff, Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨fun ⟨m, hdmpx⟩ => ?_, fun ⟨m, hmp, himx⟩ => ⟨m, ?_⟩⟩
  · refine ⟨m, support_evalMapApplyPoly_subset x p <| mem_support_iff.2 hdmpx,
      evalMapApplyPoly_monomial i x m ▸ ne_zero_iff.2 ⟨m, ?_⟩⟩
    · have : ¬∃ e ∈ m.support, x ∉ I.g e := fun h => by
        have := coeff_evalMapApplyPoly x m p ▸ hdmpx
        simp only [h] at this
        exact this rfl
      simpa only [this, reduceIte, coeff_monomial m m i] using hi
  · refine coeff_evalMapApplyPoly x m p ▸ ?_
    · have : ¬∃ e ∈ m.support, x ∉ I.g e := fun h => by
        have := evalMapApplyPoly_monomial i x m ▸ himx
        simp only [h] at this
        exact this rfl
      simp only [this]
      exact mem_support_iff.1 hmp

lemma evalMapApplyPoly_support_eq_biUnion_biInter
    {k : Type*} [Field k] {I : SWICat} (p : MvPolynomial I.E k) :
    { x : I.X | evalMapApplyPoly x p ≠ 0 } =
      ⋃ m ∈ p.support, ⋂ e ∈ m.support, I.g e := by
  simp only [evalMapApplyPoly_support_eq_biUnion one_ne_zero p,
    evalMapApplyPoly_monomial_support_eq_biInter k one_ne_zero]

lemma isOpen_evalMapApplyPoly_support {k : Type*} [Field k]
    {I : SWICat} (p : MvPolynomial I.E k) :
    IsOpen { x : I.X | evalMapApplyPoly x p ≠ 0 } :=
  evalMapApplyPoly_support_eq_biUnion_biInter p ▸ isOpen_biUnion fun _ _ =>
    isOpen_biInter_finset fun e _ => I.forall_isOpen e

lemma isCompact_evalMapApplyPoly_support {k : Type*} [Field k]
    {I : SWICat} (p : MvPolynomial I.E k) :
    IsCompact { x : I.X | evalMapApplyPoly x p ≠ 0 } :=
  evalMapApplyPoly_support_eq_biUnion_biInter p ▸ p.support.isCompact_biUnion fun m _ =>
    (m.support.biInter_mem_of_finiteInter (finiteInter_isOpen_and_isCompact I.X)
      (fun _ ⟨e, hes⟩ => hes ▸ ⟨I.forall_isOpen e, I.forall_isCompact e⟩)).2

-- example {k : Type*} [Field k] {i : k} (hi : i ≠ 0) {I : SWICat} (x : I.X)
--     {m : { T k e | e : I.E } →₀ ℕ} {p : MvPolynomial { T k e | e : I.E } k}
--     (hmp : m ∉ p.support) :
--     ((monomial m i + p).map (Pi.ringHom fun x => C)).eval (fun s => s.1) x = 0 ↔
--       (monomial m ((Pi.ringHom fun x => C) i)).eval (fun s => s.1) x = 0 ∧
--       (p.map (Pi.ringHom fun x => C)).eval (fun s => s.1) x = 0 := by
--   have : (((monomial m) ((Pi.ringHom fun x => C) i)).eval fun s => s.1) x =
--       (((MvPolynomial.map C) (monomial m i)).eval fun s => s.1 x) :=
--     eval_map_ringHom_apply_eq_eval_map_C_apply x (monomial m i) ▸
--       map_monomial (Pi.ringHom fun x => C) m i ▸ rfl
--   refine eval_map_ringHom_apply_eq_eval_map_C_apply x (monomial m i + p) ▸ this ▸
--     eval_map_ringHom_apply_eq_eval_map_C_apply x p ▸ map_add (MvPolynomial.map C) _ p ▸
--     eval_add (f := fun s : { T k e | e : I.E } => s.1 x) ▸
--     ⟨?_, fun ⟨himx, hpx⟩ => himx.symm ▸ hpx.symm ▸ zero_add 0⟩
--   · refine (p.map C).eval_eq (fun s => s.1 x) ▸ p.support_map_of_injective (C_injective I.E k) ▸
--       map_monomial C m i ▸ eval_monomial (f := fun s : { T k e | e : I.E } => s.1 x) ▸ sorry

lemma springLike' (k : Type*) [Field k] (I : SWICat) :
    SpringLike' (Subring.closure ((Pi.ringHom fun _ => C).range.carrier ∪
      { T k e | e : I.E })) where
  spectralSpace := I.spectralSpace
  forall_isOpen := fun a ha => by
    obtain ⟨p, hap⟩ := exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure
      (le_refl _) (Set.Subset.refl _) ha
    exact hap ▸ isOpen_evalMapApplyPoly_support p
  forall_isCompact := fun a ha => by
    obtain ⟨p, hap⟩ := exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure
      (le_refl _) (Set.Subset.refl _) ha
    exact hap ▸ isCompact_evalMapApplyPoly_support p
  isTopologicalBasis := by
    refine (isTopologicalBasis_of_subbasis I.eq_generateFrom).of_isOpen_of_subset
      (fun s ⟨a, ha, has⟩ => ?_) (fun s ⟨S, ⟨hS, hIS⟩, hSs⟩ => ?_)
    · obtain ⟨p, hap⟩ := exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure
        (le_refl _) (Set.Subset.refl _) ha
      exact has ▸ hap ▸ isOpen_evalMapApplyPoly_support p
    · choose f hf using fun s : hS.toFinset => hIS <| hS.mem_toFinset.mp s.2
      refine ⟨∏ s : hS.toFinset, T k (f s), ?_, ?_⟩
      · exact prod_mem fun s _ => mem_closure_of_mem <| Or.intro_right _ ⟨f s, rfl⟩
      · ext
        simp only [univ_eq_attach, ← hSs, prod_T_support_eq_biInter, hf, mem_attach,
          Set.iInter_true, Set.mem_iInter, Subtype.forall, hS.mem_toFinset, Set.mem_sInter]

noncomputable def closureRangeUnionIsSimple (k : Type*) [Field k]
    (I : SWICat) : (I.springLike' k).isSimple where
  F := FractionRing (MvPolynomial I.E k)
  field := inferInstance
  h x := OreLocalization.numeratorRingHom
  forall_injective x := IsFractionRing.injective
    (MvPolynomial I.E k) (FractionRing (MvPolynomial I.E k))
  forall_finite a := fun ha => by
    obtain ⟨p, hap⟩ := exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure
      (le_refl _) (Set.Subset.refl _) ha
    exact hap ▸ ((finite_evalMapApplyPoly_image p).image numeratorRingHom.toFun).subset
      fun q ⟨x, hpqx⟩ => hpqx ▸ ⟨evalMapApplyPoly x p, ⟨x, rfl⟩, rfl⟩

end SWICat

namespace MvPolynomial

theorem support_mul_C_of_ne_zero {R σ : Type*} [CommSemiring R]
    [IsDomain R] {r : R} (hr : r ≠ 0) (p : MvPolynomial σ R) :
    (p * C r).support = p.support := by
  ext m
  exact (p * C r).mem_support_iff.trans <| not_iff_comm.mp <| p.notMem_support_iff.trans <|
    mul_comm p _ ▸ p.coeff_C_mul m r ▸ (mul_eq_zero_iff_left hr).symm

end MvPolynomial

namespace SWICat

open Classical in
noncomputable def valuationFun (k : Type*) [Field k] {I : SWICat} (p : σ(I.X)) :
    MvPolynomial I.E k → NNRat :=
  fun P =>
    if hP : P.support.Nonempty then
      (P.support.image fun m => ∏ i ∈ m.support, if p.z.2 ∈ I.g i then 1 else (1 / 2) ^ m i).max'
        (P.support.image_nonempty.2 hP)
    else 0

open Classical in
lemma valuationFun_apply_of_support_nonempty {k : Type*} [Field k] {I : SWICat}
    (p : σ(I.X)) {P : MvPolynomial I.E k} (hP : P.support.Nonempty) :
    valuationFun k p P = (P.support.image fun m => ∏ i ∈ m.support,
      if p.z.2 ∈ I.g i then 1 else (1 / 2) ^ m i).max' (P.support.image_nonempty.2 hP) := by
  simp [valuationFun, hP]

lemma valuationFun_apply_zero (k : Type*) [Field k] {I : SWICat} (p : σ(I.X)) :
    valuationFun k p 0 = 0 := by
  simp [valuationFun]

open Classical in
lemma prod_le_valuationFun_apply_of_mem_support {k : Type*} [Field k] {I : SWICat}
    (p : σ(I.X)) {P : MvPolynomial I.E k} {m : I.E →₀ ℕ} (hmP : m ∈ P.support) :
    ∏ i ∈ m.support, (if p.z.2 ∈ I.g i then 1 else (1 / 2) ^ m i)
      ≤ valuationFun k p P := by
  have : P.support.Nonempty := ⟨m, hmP⟩
  simp only [this, valuationFun]
  exact le_max' _ _ <| mem_image.2 ⟨m, hmP, by congr⟩

open Classical in
lemma valuationFun_apply_eq_iff {k : Type*} [Field k] {I : SWICat} (p : σ(I.X))
    {P : MvPolynomial I.E k} (hP : P.support.Nonempty) (r : NNRat) :
    valuationFun k p P = r ↔
    (∀ n ∈ P.support, (∏ i ∈ n.support, if p.z.2 ∈ I.g i then 1 else (1 / 2) ^ n i) ≤ r) ∧
      ∃ m ∈ P.support, ∏ i ∈ m.support, (if p.z.2 ∈ I.g i then 1 else (1 / 2) ^ m i) = r := by
  refine ⟨fun hPpr => ⟨fun n hnP => ?_, ?_⟩, fun ⟨hPpr, m, hmP, hmr⟩ => ?_⟩
  · exact hPpr ▸ prod_le_valuationFun_apply_of_mem_support p hnP
  · by_contra h
    have : valuationFun k p P < r := by
      refine valuationFun_apply_of_support_nonempty p hP ▸ (max'_lt_iff _ _).2 fun q hPq => ?_
      · obtain ⟨m, hmP, hmpq⟩ := (mem_image ..).1 hPq
        exact hmpq ▸ lt_of_le_of_ne (hPpr ▸ prod_le_valuationFun_apply_of_mem_support p hmP)
          ((not_and.1 <| not_exists.1 h m) hmP)
    exact (ne_of_lt this) hPpr
  · refine valuationFun_apply_of_support_nonempty p hP ▸
      (max'_eq_iff _ _ r).2 ⟨mem_image.2 ⟨m, hmP, by congr⟩, fun q hPqm => ?_⟩
    · obtain ⟨n, hnP, hnpq⟩ := mem_image.1 hPqm
      exact hnpq ▸ hPpr n hnP

open Classical in
lemma valuationFun_apply_eq_of_forall_prod_eq {k : Type*} [Field k] {I : SWICat}
    {p : σ(I.X)} {P : MvPolynomial I.E k} (hP : P.support.Nonempty) {r : NNRat}
    (hPpr : ∀ m ∈ P.support, (∏ i ∈ m.support, if p.z.2 ∈ I.g i then 1 else (1 / 2) ^ m i) = r) :
    valuationFun k p P = r := by
  refine (valuationFun_apply_eq_iff p hP r).2 ⟨fun n hnP => le_of_eq <| hPpr n hnP, ?_⟩
  · obtain ⟨m, hmP⟩ := hP
    exact ⟨m, hmP, hPpr m hmP⟩

open Classical in
lemma valuationFun_apply_add_eq_apply_of_lt {k : Type*} [Field k] {I : SWICat} (p : σ(I.X))
    {P Q : MvPolynomial I.E k} (hPQ : I.valuationFun k p P < I.valuationFun k p Q) :
    I.valuationFun k p (P + Q) = I.valuationFun k p Q := by
  have hQ : Q.support.Nonempty :=
    Q.support_nonempty.2 fun hQ => not_lt_zero <| (hQ ▸ valuationFun_apply_zero k p) ▸ hPQ
  by_cases hP : P.support.Nonempty
  · obtain ⟨hpQ1, m, hmQ, hpQ2⟩ := (valuationFun_apply_eq_iff p hQ _).1 rfl
    have : m ∈ (P + Q).support := mem_support_iff.2 <| coeff_add m P Q ▸ fun h => by
      have : m ∈ P.support := mem_support_iff.2 fun hmP =>
        (mem_support_iff.1 hmQ) (zero_add (coeff m Q) ▸ hmP ▸ h)
      exact not_le_of_gt hPQ <| hpQ2 ▸ prod_le_valuationFun_apply_of_mem_support p this
    refine (valuationFun_apply_eq_iff p ⟨m, this⟩ _).2 ⟨fun n hnPQ => ?_, ⟨m, this, hpQ2⟩⟩
    · refine (mem_union.1 <| P.support_add hnPQ).elim (fun hnP => ?_) (fun hnQ => ?_)
      · exact le_of_lt <| lt_of_le_of_lt (prod_le_valuationFun_apply_of_mem_support p hnP) hPQ
      · exact prod_le_valuationFun_apply_of_mem_support p hnQ
  · exact (of_not_not <| (not_iff_not.2 support_nonempty).1 hP) ▸ (zero_add Q).symm ▸ rfl

open Classical in
noncomputable def preV (k : Type*) [Field k] (I : SWICat) :
    Π p : σ(I.X), Valuation (MvPolynomial I.E k) NNRat :=
  fun p => {
    toFun := fun P =>
      if H : P.support.Nonempty then
        (P.support.image fun m => ∏ i ∈ m.support, if p.z.2 ∈ I.g i then 1 else (1 / 2) ^ m i).max'
          (P.support.image_nonempty.2 H)
      else 0
    map_zero' := by simp only [MvPolynomial.support_zero, Finset.not_nonempty_empty, reduceDIte]
    map_one' := by simp only [← C_1, support_C, one_ne_zero, reduceIte, singleton_nonempty,
      reduceDIte, image_singleton, Finsupp.support_zero, prod_empty, max'_singleton]
    map_mul' := fun P Q => by
      by_cases HPQ : (P * Q).support.Nonempty
      · obtain ⟨hP, hQ⟩ := mul_ne_zero_iff.1 <| support_nonempty.1 HPQ
        have HP := support_nonempty.2 hP
        have HQ := support_nonempty.2 hQ
        simp only [HPQ, reduceDIte, one_div, HP, HQ]
        sorry
      · refine (mul_eq_zero.1 <| support_nonempty.not_left.1 HPQ).elim (fun hP => ?_) (fun hQ => ?_)
        · simp only [hP, zero_mul, MvPolynomial.support_zero, Finset.not_nonempty_empty, reduceDIte,
            mul_dite, dite_eq_ite, ite_self]
        · simp only [hQ, mul_zero, MvPolynomial.support_zero, Finset.not_nonempty_empty, reduceDIte]
    map_add_le_max' := sorry
  }

end SWICat
