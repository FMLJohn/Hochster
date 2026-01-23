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
      (P.support.image fun m => ∏ e ∈ m.support, if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ m e).max'
        (P.support.image_nonempty.2 hP)
    else 0

open Classical in
lemma valuationFun_apply_of_support_nonempty {k : Type*} [Field k] {I : SWICat}
    (p : σ(I.X)) {P : MvPolynomial I.E k} (hP : P.support.Nonempty) :
    valuationFun k p P = (P.support.image fun m => ∏ e ∈ m.support,
      if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ m e).max' (P.support.image_nonempty.2 hP) := by
  simp [valuationFun, hP]

lemma valuationFun_apply_zero (k : Type*) [Field k] {I : SWICat} (p : σ(I.X)) :
    valuationFun k p 0 = 0 := by
  simp [valuationFun]

open Classical in
lemma valuationFun_apply_C {k : Type*} [Field k] (i : k) {I : SWICat} (p : σ(I.X)) :
    valuationFun k p (C i) = if i = 0 then 0 else 1 := by
  by_cases hi : i = 0
  · exact hi.symm ▸ @C_0 k I.E _ ▸ valuationFun_apply_zero k p ▸ (if_pos rfl).symm
  · exact valuationFun_apply_of_support_nonempty p (support_nonempty.2 <| C_ne_zero.2 hi) ▸
      if_neg hi ▸ by
      simp only [one_div, inv_pow, support_C i, if_neg hi, image_singleton, Finsupp.coe_zero,
        Pi.zero_apply, pow_zero, inv_one, ite_self, prod_const_one, max'_singleton]

open Classical in
lemma valuationFun_apply_X (k : Type*) [Field k] {I : SWICat} (e : I.E) (p : σ(I.X)) :
    valuationFun k p (MvPolynomial.X e) = if p.z.2 ∈ I.g e then 1 else 1 / 2 := by
  refine valuationFun_apply_of_support_nonempty p
    (support_nonempty.2 <| @X_ne_zero k I.E _ _ e) ▸ ?_
  . have : (Finsupp.single e 1).support = {e} := by
      ext d
      exact (Finsupp.mem_support_single d e 1).trans
        ⟨fun ⟨hde, h⟩ => mem_singleton.2 hde, fun hde => ⟨mem_singleton.1 hde, one_ne_zero⟩⟩
    simp only [support_X, image_singleton, max'_singleton, Finsupp.single_apply, this, pow_one,
      prod_singleton, reduceIte]

open Classical in
lemma valuationFun_apply_monomial {k : Type*} [Field k]
    (i : k) {I : SWICat} (p : σ(I.X)) (m : I.E →₀ ℕ) :
    valuationFun k p (monomial m i) =
      if i = 0 then 0 else ∏ e ∈ m.support, if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ m e := by
  by_cases hi : i = 0
  · simpa only [hi, monomial_zero] using valuationFun_apply_zero k p
  · simp only [valuationFun, support_monomial, hi, reduceIte, singleton_nonempty, reduceDIte,
      image_singleton, max'_singleton]

open Classical in
lemma prod_le_valuationFun_apply_of_mem_support {k : Type*} [Field k] {I : SWICat}
    (p : σ(I.X)) {P : MvPolynomial I.E k} {m : I.E →₀ ℕ} (hmP : m ∈ P.support) :
    ∏ e ∈ m.support, (if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ m e)
      ≤ valuationFun k p P := by
  have : P.support.Nonempty := ⟨m, hmP⟩
  simp only [this, valuationFun]
  exact le_max' _ _ <| mem_image.2 ⟨m, hmP, by congr⟩

open Classical in
lemma valuationFun_apply_eq_iff_of_support_nonempty {k : Type*} [Field k] {I : SWICat}
    (p : σ(I.X)) {P : MvPolynomial I.E k} (hP : P.support.Nonempty) (r : NNRat) :
    valuationFun k p P = r ↔
    (∀ n ∈ P.support, (∏ e ∈ n.support, if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ n e) ≤ r) ∧
      ∃ m ∈ P.support, ∏ e ∈ m.support, (if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ m e) = r := by
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

lemma valuationFun_apply_eq_iff_of_support_nonempty' {k : Type*} [Field k] {I : SWICat}
    (p : σ(I.X)) {P : MvPolynomial I.E k} (hP : P.support.Nonempty) (r : NNRat) :
    valuationFun k p P = r ↔
    (∀ n ∈ P.support, valuationFun k p (monomial n 1) ≤ r) ∧
      ∃ m ∈ P.support, valuationFun k p (monomial m 1) = r := by
  simp only [valuationFun_apply_monomial, one_ne_zero]
  exact valuationFun_apply_eq_iff_of_support_nonempty p hP r

open Classical in
lemma valuationFun_apply_eq_iff_of_ne_zero {k : Type*} [Field k] {I : SWICat}
    (p : σ(I.X)) (P : MvPolynomial I.E k) {r : NNRat} (hr : r ≠ 0) :
    valuationFun k p P = r ↔
    (∀ n ∈ P.support, (∏ e ∈ n.support, if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ n e) ≤ r) ∧
      ∃ m ∈ P.support, ∏ e ∈ m.support, (if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ m e) = r := by
  refine ⟨fun hPpr => ?_, fun h => ?_⟩
  · refine (valuationFun_apply_eq_iff_of_support_nonempty p ?_ r).1 hPpr
    · exact support_nonempty.2 fun hP => hr <| hPpr ▸ hP ▸ valuationFun_apply_zero k p
  · refine (valuationFun_apply_eq_iff_of_support_nonempty p ?_ r).2 h
    · obtain ⟨m, hmP, _⟩ := h.2
      exact ⟨m, hmP⟩

lemma valuationFun_apply_eq_iff_of_ne_zero' {k : Type*} [Field k] {I : SWICat}
    (p : σ(I.X)) (P : MvPolynomial I.E k) {r : NNRat} (hr : r ≠ 0) :
    valuationFun k p P = r ↔
    (∀ n ∈ P.support, valuationFun k p (monomial n 1) ≤ r) ∧
      ∃ m ∈ P.support, valuationFun k p (monomial m 1) = r := by
  simp only [valuationFun_apply_monomial, one_ne_zero]
  exact valuationFun_apply_eq_iff_of_ne_zero p P hr

open Classical in
lemma valuationFun_apply_eq_zero_iff {k : Type*} [Field k]
    {I : SWICat} (p : σ(I.X)) (P : MvPolynomial I.E k) :
    valuationFun k p P = 0 ↔ P = 0 := by
  refine ⟨fun hPp => ?_, fun hP => hP ▸ valuationFun_apply_zero k p⟩
  · by_contra hP
    obtain ⟨m, hmP⟩ := support_nonempty.2 hP
    obtain ⟨e, hem, hemp⟩ := prod_eq_zero_iff.1
      (eq_of_ge_of_le (((valuationFun_apply_eq_iff_of_support_nonempty p
      (support_nonempty.2 hP) 0).1 hPp).1 m hmP) (zero_le _)).symm
    have : (if p.z.2 ∈ I.g e then (1 : NNRat) else (1 / 2) ^ m e) ≠ 0 := by
      by_cases hep : p.z.2 ∈ I.g e
      · simp only [hep, reduceIte, ne_eq, one_ne_zero, not_false_eq_true]
      · simp only [hep, reduceIte, one_div, ne_eq, inv_eq_zero, pow_eq_zero_iff',
          OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
    exact this hemp

open Classical in
lemma valuationFun_apply_eq_of_forall_prod_eq {k : Type*} [Field k] {I : SWICat}
    {p : σ(I.X)} {P : MvPolynomial I.E k} (hP : P.support.Nonempty) {r : NNRat}
    (hPpr : ∀ m ∈ P.support, (∏ e ∈ m.support, if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ m e) = r) :
    valuationFun k p P = r := by
  refine (valuationFun_apply_eq_iff_of_support_nonempty p hP r).2
    ⟨fun n hnP => le_of_eq <| hPpr n hnP, ?_⟩
  · obtain ⟨m, hmP⟩ := hP
    exact ⟨m, hmP, hPpr m hmP⟩

lemma valuationFun_apply_eq_of_forall_valuationFun_apply_eq {k : Type*} [Field k]
    {I : SWICat} {p : σ(I.X)} {P : MvPolynomial I.E k} (hP : P.support.Nonempty)
    {r : NNRat} (hPpr : ∀ m ∈ P.support, valuationFun k p (monomial m 1) = r) :
    valuationFun k p P = r :=
  valuationFun_apply_eq_of_forall_prod_eq hP fun m hmP => hPpr m hmP ▸
    valuationFun_apply_monomial (k := k) 1 p m ▸ by simp only [one_ne_zero, reduceIte]

open Classical in
lemma valuationFun_apply_le_iff_forall_prod_le {k : Type*} [Field k]
    {I : SWICat} (p : σ(I.X)) (P : MvPolynomial I.E k) (r : NNRat) :
    valuationFun k p P ≤ r ↔
    ∀ n ∈ P.support, (∏ e ∈ n.support, if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ n e) ≤ r := by
  by_cases hP : P.support.Nonempty
  · simp only [valuationFun, hP, reduceDIte, max'_le_iff, mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
  · simp only [valuationFun, not_nonempty_iff_eq_empty.1 hP, notMem_empty, IsEmpty.forall_iff,
      implies_true, Finset.not_nonempty_empty, reduceDIte, zero_le]

lemma valuationFun_apply_le_iff_forall_valuationFun_apply_le {k : Type*}
    [Field k] {I : SWICat} (p : σ(I.X)) (P : MvPolynomial I.E k) (r : NNRat) :
    valuationFun k p P ≤ r ↔
    ∀ n ∈ P.support, valuationFun k p (monomial n 1) ≤ r := by
  simp only [valuationFun_apply_monomial, one_ne_zero]
  exact valuationFun_apply_le_iff_forall_prod_le p P r

open Classical in
lemma valuationFun_apply_lt_iff_forall_prod_lt_of_support_nonempty {k : Type*} [Field k]
    {I : SWICat} (p : σ(I.X)) {P : MvPolynomial I.E k} (hP : P.support.Nonempty) (r : NNRat) :
    valuationFun k p P < r ↔
    ∀ n ∈ P.support, (∏ e ∈ n.support, if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ n e) < r :=
  valuationFun_apply_of_support_nonempty p hP ▸ by
    simp only [max'_lt_iff, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

lemma valuationFun_apply_lt_iff_forall_valuationFun_apply_lt_of_support_nonempty
    {k : Type*} [Field k] {I : SWICat} (p : σ(I.X)) {P : MvPolynomial I.E k}
    (hP : P.support.Nonempty) (r : NNRat) :
    valuationFun k p P < r ↔
    ∀ n ∈ P.support, valuationFun k p (monomial n 1) < r := by
  simp only [valuationFun_apply_monomial, one_ne_zero]
  exact valuationFun_apply_lt_iff_forall_prod_lt_of_support_nonempty p hP r

open Classical in
lemma valuationFun_apply_lt_iff_forall_prod_lt_of_ne_zero {k : Type*} [Field k]
    {I : SWICat} (p : σ(I.X)) (P : MvPolynomial I.E k) {r : NNRat} (hr : r ≠ 0) :
    valuationFun k p P < r ↔
    ∀ n ∈ P.support, (∏ e ∈ n.support, if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ n e) < r := by
  by_cases hP : P.support.Nonempty
  · simp only [valuationFun, hP, reduceDIte, max'_lt_iff, mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
  · simp only [valuationFun, not_nonempty_iff_eq_empty.1 hP, notMem_empty, IsEmpty.forall_iff,
      implies_true, iff_true]
    exact pos_of_ne_zero hr

lemma valuationFun_apply_lt_iff_forall_valuationFun_apply_lt_of_ne_zero {k : Type*}
    [Field k] {I : SWICat} (p : σ(I.X)) (P : MvPolynomial I.E k) {r : NNRat} (hr : r ≠ 0) :
    valuationFun k p P < r ↔
    ∀ n ∈ P.support, valuationFun k p (monomial n 1) < r := by
  simp only [valuationFun_apply_monomial, one_ne_zero]
  exact valuationFun_apply_lt_iff_forall_prod_lt_of_ne_zero p P hr

open Classical in
lemma valuationFun_apply_add_le_max {k : Type*} [Field k]
    {I : SWICat} (p : σ(I.X)) (P Q : MvPolynomial I.E k) :
    valuationFun k p (P + Q) ≤ max (valuationFun k p P) (valuationFun k p Q) := by
  refine (valuationFun_apply_le_iff_forall_prod_le p (P + Q) _).2 fun n hnPQ =>
    (mem_union.1 <| support_add hnPQ).elim (fun hnP => ?_) (fun hnQ => ?_)
  · exact (prod_le_valuationFun_apply_of_mem_support p hnP).trans (le_max_left ..)
  · exact (prod_le_valuationFun_apply_of_mem_support p hnQ).trans (le_max_right ..)

open Classical in
lemma valuationFun_apply_add_eq_apply_of_lt {k : Type*} [Field k] {I : SWICat} (p : σ(I.X))
    {P Q : MvPolynomial I.E k} (hPQ : valuationFun k p P < valuationFun k p Q) :
    valuationFun k p (P + Q) = valuationFun k p Q := by
  have hQ : Q.support.Nonempty :=
    Q.support_nonempty.2 fun hQ => not_lt_zero <| (hQ ▸ valuationFun_apply_zero k p) ▸ hPQ
  by_cases hP : P.support.Nonempty
  · obtain ⟨hpQ1, m, hmQ, hpQ2⟩ := (valuationFun_apply_eq_iff_of_support_nonempty p hQ _).1 rfl
    have : m ∈ (P + Q).support := mem_support_iff.2 <| coeff_add m P Q ▸ fun h => by
      have : m ∈ P.support := mem_support_iff.2 fun hmP =>
        (mem_support_iff.1 hmQ) (zero_add (coeff m Q) ▸ hmP ▸ h)
      exact not_le_of_gt hPQ <| hpQ2 ▸ prod_le_valuationFun_apply_of_mem_support p this
    refine (valuationFun_apply_eq_iff_of_support_nonempty p ⟨m, this⟩ _).2
      ⟨fun n hnPQ => ?_, ⟨m, this, hpQ2⟩⟩
    · refine (mem_union.1 <| P.support_add hnPQ).elim (fun hnP => ?_) (fun hnQ => ?_)
      · exact le_of_lt <| lt_of_le_of_lt (prod_le_valuationFun_apply_of_mem_support p hnP) hPQ
      · exact prod_le_valuationFun_apply_of_mem_support p hnQ
  · exact (of_not_not <| (not_iff_not.2 support_nonempty).1 hP) ▸ (zero_add Q).symm ▸ rfl

open Classical in
lemma valuationFun_apply_eq_iff_exist_of_support_nonempty {k : Type*} [Field k] {I : SWICat}
    (p : σ(I.X)) {P : MvPolynomial I.E k} (hP : P.support.Nonempty) (r : NNRat) :
    valuationFun k p P = r ↔
    ∃ Q R : MvPolynomial I.E k, P = Q + R ∧ valuationFun k p Q < r ∧
      R.support.Nonempty ∧ ∀ m ∈ R.support, valuationFun k p (monomial m 1) = r := by
  have : (∑ m ∈ P.support with valuationFun k p (monomial m 1) = r,
      coeff m P • monomial m (1 : k)).support =
      P.support.filter fun m => valuationFun k p (monomial m 1) = r := by
    ext m
    simp only [mem_support_iff, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul, mul_ite,
      mul_one, mul_zero, sum_ite_eq', mem_filter, ne_eq, ite_eq_right_iff, and_imp,
      Classical.not_imp, and_congr_right_iff, and_iff_left_iff_imp]
    exact fun hmP _ => hmP
  refine ⟨fun hPpr => ⟨∑ m ∈ P.support.filter fun m => valuationFun k p (monomial m 1) ≠ r,
    P.coeff m • monomial m 1, ∑ m ∈ P.support.filter fun m => valuationFun k p (monomial m 1) = r,
    P.coeff m • monomial m 1, ?_, ?_, ?_, ?_⟩, fun ⟨Q, R, hPQR, hQpr, hR, hRrp⟩ => ?_⟩
  · ext
    simp only [← sum_union (disjoint_filter.2 fun m hmP hmPr => hmPr), union_comm,
      filter_union_filter_not_eq, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul, mul_ite,
      mul_one, mul_zero, sum_ite_eq', mem_support_iff, ite_not, right_eq_ite_iff, imp_self]
  · refine (valuationFun_apply_lt_iff_forall_valuationFun_apply_lt_of_ne_zero p _ fun hr =>
      P.support_nonempty_iff.1 hP <| (valuationFun_apply_eq_zero_iff p P).1 <| hr ▸ hPpr).2
      fun n hn => ?_
    · have : (∑ m ∈ P.support with valuationFun k p (monomial m 1) ≠ r,
          coeff m P • monomial m (1 : k)).support =
          P.support.filter fun m => valuationFun k p (monomial m 1) ≠ r := by
        ext m
        simp only [ne_eq, mem_support_iff, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul,
          mul_ite, mul_one, mul_zero, sum_ite_eq', mem_filter, ite_eq_right_iff, and_imp,
          Classical.not_imp, and_congr_right_iff, and_iff_left_iff_imp]
        exact fun hm _ => hm
      obtain ⟨hnP, hnpr⟩ := mem_filter.1 (this ▸ hn)
      exact lt_of_le_of_ne ((valuationFun_apply_le_iff_forall_valuationFun_apply_le p P _).1
        (le_of_eq hPpr) n hnP) hnpr
  · obtain ⟨m, hmP, hmpr⟩ := ((valuationFun_apply_eq_iff_of_support_nonempty p hP r).1 hPpr).2
    exact this.symm ▸ ⟨m, mem_filter.2 ⟨hmP, valuationFun_apply_monomial (k := k) 1 p m ▸
      if_neg (one_ne_zero (α := k)) ▸ hmpr⟩⟩
  · exact this.symm ▸ fun m hmPpr => (mem_filter.1 hmPpr).2
  · exact valuationFun_apply_eq_of_forall_valuationFun_apply_eq hR hRrp ▸
      hPQR ▸ valuationFun_apply_add_eq_apply_of_lt p
        (valuationFun_apply_eq_of_forall_valuationFun_apply_eq hR hRrp ▸ hQpr)

open Classical in
lemma valuationFun_apply_monomial_mul_monomial (k : Type*)
    [Field k] {I : SWICat} (p : σ(I.X)) (m n : I.E →₀ ℕ) :
    valuationFun k p (monomial (m + n) 1) =
    valuationFun k p (monomial m 1) * valuationFun k p (monomial n 1) := by
  have h1 : (m + n).support = m.support \ n.support ∪ n.support := by
    ext e
    simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, ne_eq, Nat.add_eq_zero_iff,
      not_and, sdiff_union_self_eq_union, mem_union]
    exact imp_iff_not_or
  have h2 : ∏ e ∈ m.support \ n.support, (if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ (m e + n e)) =
      ∏ e ∈ m.support \ n.support, (if p.z.2 ∈ I.g e then (1 : NNRat) else (1 / 2) ^ m e) :=
    prod_congr rfl fun e hemn => by
      rw [Finsupp.notMem_support_iff.1 (mem_sdiff.1 hemn).2, add_zero]
  have h3 : ∏ e ∈ n.support \ m.support, (if p.z.2 ∈ I.g e then 1 else (1 / 2) ^ (m e + n e)) =
      ∏ e ∈ n.support \ m.support, (if p.z.2 ∈ I.g e then (1 : NNRat) else (1 / 2) ^ n e) :=
    prod_congr rfl fun e hemn => by
      rw [Finsupp.notMem_support_iff.1 (mem_sdiff.1 hemn).2, zero_add]
  simp only [valuationFun_apply_monomial, one_ne_zero, reduceIte, Finsupp.coe_add, Pi.add_apply]
  rw [← sdiff_union_inter m.support n.support, prod_union (disjoint_sdiff_inter ..), mul_assoc, h1,
    prod_union sdiff_disjoint, h2]
  refine mul_eq_mul_left_iff.2 <| Or.intro_left _ ?_
  · nth_rw 1 3 [← sdiff_union_inter n.support m.support]
    rw [prod_union (disjoint_sdiff_inter ..), prod_union (disjoint_sdiff_inter ..),
      n.support.inter_comm, h3, mul_comm (∏ x ∈ m.support ∩ n.support, _), mul_assoc]
    refine mul_eq_mul_left_iff.2 <| Or.intro_left _ <| (prod_mul_distrib (M := NNRat)).symm ▸
      prod_congr rfl fun e hemn => ?_
    · by_cases hep : p.z.2 ∈ I.g e
      · simp only [hep, reduceIte, mul_one]
      · simp only [hep, reduceIte, pow_add, add_comm (m e)]

open Classical in
lemma valuationFun_apply_mul_eq_of_forall_of_forall {k : Type*}
    [Field k] {I : SWICat} (p : σ(I.X)) {P Q : MvPolynomial I.E k}
    (hP : P.support.Nonempty) (hQ : Q.support.Nonempty) {r s : NNRat}
    (hPpr : ∀ m ∈ P.support, valuationFun k p (monomial m 1) = r)
    (hQps : ∀ m ∈ Q.support, valuationFun k p (monomial m 1) = s) :
    valuationFun k p (P * Q) = r * s := by
  refine valuationFun_apply_eq_of_forall_valuationFun_apply_eq ?_ fun m hmPQ => ?_
  · exact (P * Q).support_nonempty_iff.2 <| mul_ne_zero (M₀ := MvPolynomial I.E k)
      (P.support_nonempty_iff.1 hP) (Q.support_nonempty_iff.1 hQ)
  · obtain ⟨l, hlP, n, hnQ, hlmn⟩ := mem_add.1 <| support_mul P Q hmPQ
    exact hlmn ▸ valuationFun_apply_monomial_mul_monomial k p l n ▸ hPpr l hlP ▸ hQps n hnQ ▸ rfl

open Classical in
lemma valuationFun_apply_mul_le_mul {k : Type*} [Field k]
    {I : SWICat} (p : σ(I.X)) (P Q : MvPolynomial I.E k) :
    valuationFun k p (P * Q) ≤ valuationFun k p P * valuationFun k p Q := by
  refine (valuationFun_apply_le_iff_forall_prod_le p (P * Q) _).2 fun n hnPQ => ?_
  · obtain ⟨l, hlP, m, hmQ, hlmn⟩ := mem_add.1 <| P.support_mul Q hnPQ
    refine hlmn ▸ (if_neg (one_ne_zero (α := k)) ▸ valuationFun_apply_monomial (k := k) 1 p _ ▸
      valuationFun_apply_monomial_mul_monomial k p l m) ▸ mul_le_mul ?_ ?_ (zero_le _) (zero_le _)
    · exact (valuationFun_apply_le_iff_forall_valuationFun_apply_le p P _).1 (le_of_eq rfl) l hlP
    · exact (valuationFun_apply_le_iff_forall_valuationFun_apply_le p Q _).1 (le_of_eq rfl) m hmQ

lemma valuationFun_apply_mul {k : Type*} [Field k]
    {I : SWICat} (p : σ(I.X)) (P Q : MvPolynomial I.E k) :
    valuationFun k p (P * Q) = valuationFun k p P * valuationFun k p Q := by
  by_cases hP : P.support.Nonempty
  · by_cases hQ : Q.support.Nonempty
    · obtain ⟨R1, S1, hPRS, hPRp, hS1, hPSp⟩ :=
        (valuationFun_apply_eq_iff_exist_of_support_nonempty p hP _).1 rfl
      obtain ⟨R2, S2, hQRS, hQRp, hS2, hQSp⟩ :=
        (valuationFun_apply_eq_iff_exist_of_support_nonempty p hQ _).1 rfl
      have hS : valuationFun k p (S1 * S2) = valuationFun k p P * valuationFun k p Q :=
        valuationFun_apply_mul_eq_of_forall_of_forall p hS1 hS2 hPSp hQSp
      have hP' : 0 < valuationFun k p P := pos_of_ne_zero fun hPp =>
        P.support_nonempty_iff.1 hP <| (valuationFun_apply_eq_zero_iff p P).1 hPp
      have hQ' : 0 < valuationFun k p Q := pos_of_ne_zero fun hQp =>
        Q.support_nonempty_iff.1 hQ <| (valuationFun_apply_eq_zero_iff p Q).1 hQp
      nth_rw 1 [hPRS, hQRS, mul_add, add_mul, add_mul, ← add_assoc, ← hS]
      refine valuationFun_apply_add_eq_apply_of_lt p <| lt_of_le_of_lt
        (valuationFun_apply_add_le_max p (R1 * R2 + S1 * R2) (R1 * S2)) <| max_lt ?_ ?_
      · refine lt_of_le_of_lt (valuationFun_apply_add_le_max p (R1 * R2) (S1 * R2)) <| max_lt ?_ ?_
        · refine lt_of_le_of_lt (valuationFun_apply_mul_le_mul p R1 R2) <| hS ▸ ?_
          · by_cases hRp : 0 < valuationFun k p R1
            · exact mul_lt_mul_of_pos hPRp hQRp hRp hQ'
            · exact eq_of_le_of_ge (zero_le _) (le_of_not_gt hRp) ▸
                (zero_mul (valuationFun k p R2)).symm ▸ mul_pos hP' hQ'
        · exact lt_of_le_of_lt (valuationFun_apply_mul_le_mul p S1 R2) <| hS ▸
            (valuationFun_apply_eq_of_forall_valuationFun_apply_eq hS1 hPSp).symm ▸
            mul_lt_mul' (le_of_eq rfl) hQRp (zero_le _) hP'
      · exact lt_of_le_of_lt (valuationFun_apply_mul_le_mul p R1 S2) <| hS ▸
          (valuationFun_apply_eq_of_forall_valuationFun_apply_eq hS2 hQSp).symm ▸
          mul_lt_mul hPRp (le_of_eq rfl) hQ' (zero_le _)
    · exact (iff_not_comm.2 support_nonempty).2 hQ ▸ valuationFun_apply_zero k p ▸
        (mul_zero P).symm ▸ (mul_zero (valuationFun k p P)).symm ▸ valuationFun_apply_zero k p
  · exact (iff_not_comm.2 support_nonempty).2 hP ▸ valuationFun_apply_zero k p ▸
      (zero_mul Q).symm ▸ (zero_mul (valuationFun k p Q)).symm ▸ valuationFun_apply_zero k p

lemma valuationFun_apply_le_one {k : Type*} [Field k]
    {I : SWICat} (p : σ(I.X)) (P : MvPolynomial I.E k) :
    valuationFun k p P ≤ 1 := by
  simp only [valuationFun, one_div, inv_pow]
  by_cases hP : P.support.Nonempty
  · simp only [hP, reduceDIte, max'_le_iff, mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    refine fun m hmP => prod_induction _ (fun r => r ≤ 1)
      (fun r s hr hs => mul_le_one₀ hr (zero_le _) hs) (NNRat.coe_le_coe.1 rfl) (fun e hem => ?_)
    · by_cases hep : p.z.2 ∈ I.g e
      · exact if_pos hep ▸ NNRat.coe_le_coe.1 rfl
      · exact if_neg hep ▸ (inv_le_one₀ (pow_pos rfl (m e))).2 (one_le_pow₀ one_le_two)
  · simp only [hP, reduceDIte, zero_le]

lemma exists_valuationFun_apply_eq_two_pow_of_ne_zero {k : Type*} [Field k]
    {I : SWICat} (p : σ(I.X)) {P : MvPolynomial I.E k} (hP : P ≠ 0) :
    ∃ n : ℤ, valuationFun k p P = 2 ^ n := by
  obtain ⟨m, _ , hPpm⟩ := ((valuationFun_apply_eq_iff_of_support_nonempty p (support_nonempty.2 hP)
    (valuationFun k p P)).1 rfl).2
  refine hPpm ▸ prod_induction _ (fun r => ∃ n : ℤ, r = 2 ^ n) (fun r s ⟨m, hmr⟩ ⟨n, hns⟩ => ?_)
    ⟨0, rfl⟩ (fun e hem => ?_)
  · exact ⟨m + n, hmr ▸ hns ▸ (zpow_add₀ (NeZero.ne' 2).symm m n).symm⟩
  · by_cases hep : p.z.2 ∈ I.g e
    · exact if_pos hep ▸ ⟨0, rfl⟩
    · exact if_neg hep ▸ ⟨- m e, one_div (2 : NNRat) ▸ inv_pow (2 : NNRat) (m e) ▸
        zpow_neg (2 : NNRat) (m e) ▸ rfl⟩

noncomputable def preV (k : Type*) [Field k] (I : SWICat) :
    Π _ : σ(I.X), Valuation (MvPolynomial I.E k) NNRat :=
  fun p => {
    toFun := valuationFun k p
    map_zero' := valuationFun_apply_zero k p
    map_one' := @C_1 k I.E _ ▸ valuationFun_apply_C (1 : k) p ▸ if_neg (one_ne_zero (α := k))
    map_mul' P Q := valuationFun_apply_mul p P Q
    map_add_le_max' P Q := valuationFun_apply_add_le_max p P Q }

noncomputable def v (k : Type*) [Field k] (I : SWICat) :
    Π _ : σ(I.X), Valuation (FractionRing (MvPolynomial I.E k)) NNRat :=
  fun p => (preV k I p).extendToLocalization (S := nonZeroDivisors (MvPolynomial I.E k))
    (fun P hP => Ideal.mem_primeCompl_iff.2 <|
      (not_iff_not.2 (valuationFun_apply_eq_zero_iff p P)).2 (mem_nonZeroDivisors_iff_ne_zero.1 hP))
    (FractionRing (MvPolynomial I.E k))

lemma v_apply_ringHomToPiFractionRing_apply (k : Type*) [Field k]
    {I : SWICat} (p : σ(I.X)) (a : I.X → MvPolynomial I.E k) :
    I.v k p (Pi.ringHomToPiFractionRing (fun _ => MvPolynomial I.E k) a p.z.1) =
      I.preV k p (a p.z.1) :=
  extendToLocalization_apply_map_apply _ _ (FractionRing (MvPolynomial I.E k)) (a p.z.1)

lemma v_apply_ringHomToPiFractionRing_apply' (k : Type*) [Field k]
    {I : SWICat} (p : σ(I.X)) (a : I.X → MvPolynomial I.E k) :
    I.v k p (Pi.ringHomToPiFractionRing (fun _ => MvPolynomial I.E k) a p.z.2) =
      I.preV k p (a p.z.2) :=
  extendToLocalization_apply_map_apply _ _ (FractionRing (MvPolynomial I.E k)) (a p.z.2)

open Classical in
lemma springLike'_mapRingHomToPiFractionRing_isIndex (k : Type*) [Field k] (I : SWICat) :
    (I.springLike' k).mapRingHomToPiFractionRing.isIndex (I.v k) where
  forall_exists_of_ne_zero p a := by sorry
    -- refine Localization.induction_on (a p.z.1) fun (P, Q) hPQ => ?_
    -- · simp only [v, preV, FractionRing.mk_eq_div, map_div₀, extendToLocalization_apply_map_apply,
    --     coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    --   obtain ⟨n, hPpn⟩ := exists_valuationFun_apply_eq_two_pow_of_ne_zero p fun hP : P = 0 =>
    --     false_of_ne <| Localization.mk_zero Q ▸ hP ▸ hPQ
    --   obtain ⟨m, hQpm⟩ := exists_valuationFun_apply_eq_two_pow_of_ne_zero p
    --     (nonZeroDivisors.coe_ne_zero Q)
    --   exact hPpn ▸ hQpm ▸ ⟨n - m, (zpow_sub₀ (NeZero.ne' 2).symm n m).symm⟩
  forall_le_of_ne p a ha _ := by sorry
    -- obtain ⟨b, hb, hab⟩ := ha
    -- refine hab ▸ v_apply_ringHomToPiFractionRing_apply k p b ▸ ?_
    -- · simpa only [preV] using valuationFun_apply_le_one p (b p.z.1)
  forall_iff_of_ne p a ha hap := by sorry
    -- obtain ⟨b, hb, hab⟩ := ha
    -- obtain ⟨P, hPb⟩ := exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure
    --   (le_refl _) (Set.Subset.refl _) hb
    -- refine hab ▸ v_apply_ringHomToPiFractionRing_apply k p b ▸
    --   ((not_iff_not.2 <| to_map_eq_zero_iff (x := b p.z.2)).trans
    --     (hPb ▸ ((Set.ext_iff.1 <| evalMapApplyPoly_support_eq_biUnion_biInter P) p.z.2).trans
    --       ⟨fun ⟨s, ⟨m, hPms⟩, hps⟩ => ?_, fun hPp => ?_⟩)).symm
    -- · have hPpm := hPms ▸ hps
    --   simp only [Set.mem_iUnion, Set.mem_iInter] at hPpm
    --   obtain ⟨hmP, hmp⟩ := hPpm
    --   have hPpm : m ∈ (evalMapApplyPoly p.z.1 P).support := by
    --     refine mem_coe.1 <| support_evalMapApplyPoly p.z.1 P ▸ ⟨hmP, fun e hem => ?_⟩
    --     · by_contra hpe
    --       exact hpe <| Set.inter_singleton_nonempty.mp <| (mem_closure_iff.1 <| p.mem_closure)
    --         (I.g e) (I.forall_isOpen e) (hmp e hem)
    --   refine (valuationFun_apply_eq_iff_of_support_nonempty' p ⟨m, hPpm⟩ 1).2
    --     ⟨fun n _ => ?_, ⟨m, hPpm, ?_⟩⟩
    --   · exact valuationFun_apply_le_one p (monomial n 1)
    --   · exact valuationFun_apply_monomial (k := k) 1 p m ▸ if_neg (one_ne_zero (α := k)) ▸
    --       prod_eq_one fun e hem => if_pos (hmp e hem) ▸ rfl
    -- · obtain ⟨_, m, hPpm, hmp⟩ := (valuationFun_apply_eq_iff_of_ne_zero' p
    --     (evalMapApplyPoly p.z.1 P) one_ne_zero).1 hPp
    --   simp only [Set.mem_iUnion, Set.mem_iInter]
    --   refine ⟨m, support_evalMapApplyPoly_subset p.z.1 P hPpm, fun e hem => ?_⟩
    --   · have : ∀ e ∈ m.support, (if p.z.2 ∈ I.g e then (1 : NNRat) else (1 / 2) ^ m e) = 1 := by
    --       refine (prod_eq_one_iff_of_le_one' fun e hem => ?_).1 ?_
    --       · by_cases hep : p.z.2 ∈ I.g e
    --         · exact if_pos hep ▸ rfl
    --         · exact if_neg hep ▸ pow_le_one₀ (one_div_nonneg.2 rfl) (half_le_self rfl)
    --       · exact (if_neg (one_ne_zero (α := k)) ▸ valuationFun_apply_monomial 1 p m) ▸ hmp
    --     by_contra hep
    --     · refine (ne_of_lt <| pow_lt_one₀ (zero_le (1 / 2 : NNRat)) one_half_lt_one
    --         (Finsupp.mem_support_iff.mp hem)) ?_
    --       · simpa only [hep] using this e hem
  forall_exists_le a ha := sorry

end SWICat
