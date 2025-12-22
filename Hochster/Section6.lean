import Hochster.Section5

open CategoryTheory Function MvPolynomial Subring TopologicalSpace

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

open Classical in
noncomputable def T (k : Type*) [Field k] {I : SWICat} (e : I.E) :
    I.X → MvPolynomial I.E k :=
  fun x => if x ∈ I.g e then MvPolynomial.X e else 0

open Classical in
lemma T_def (k : Type*) [Field k] {I : SWICat} (e : I.E) :
    T k e = fun x => if x ∈ I.g e then MvPolynomial.X e else 0 := rfl

lemma T_apply_support_eq_g (k : Type*) [Field k] {I : SWICat} (e : I.E) :
    { x : I.X | T k e x ≠ 0 } = I.g e := by
  simp only [T, ne_eq, ite_eq_right_iff, X_ne_zero, imp_false, not_not, Set.setOf_mem_eq]

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

lemma eval_map_ringHom_apply_eq_eval_map_C_apply {k : Type*} [Field k]
    {I : SWICat} (x : I.X) (p : MvPolynomial { T k e | e : I.E } k) :
    (p.map (Pi.ringHom fun _ => C)).eval (fun s => s.1) x =
    (p.map C).eval fun s => s.1 x := by
  refine @p.induction_on k _ _ (fun p => (p.map (Pi.ringHom fun x => C)).eval _ x =
    (p.map C).eval _) (fun i => ?_) (fun p q => ?_) (fun p T => ?_)
  · simp only [map_C, eval_C, Pi.ringHom_apply]
  · simp only [map_add]
    exact fun hp hq => hp ▸ hq ▸ rfl
  · simp only [map_mul, map_X, eval_X]
    exact fun hp => hp ▸ rfl

lemma eval_map_ringHom_apply_eq_eval_map_C_apply' {k : Type*} [Field k]
    {I : SWICat} (x : I.X) (p : MvPolynomial I.E k) :
    (p.map (Pi.ringHom fun _ => C)).eval (fun e => T k e) x =
    (p.map C).eval fun e => T k e x := by
  refine @p.induction_on k _ _ (fun p => (p.map (Pi.ringHom fun x => C)).eval _ x =
    (p.map C).eval _) (fun i => ?_) (fun p q => ?_) (fun p _ => ?_)
  · simp only [map_C, eval_C, Pi.ringHom_apply]
  · simp only [map_add]
    exact fun hp hq => hp ▸ hq ▸ rfl
  · simp only [map_mul, map_X, eval_X]
    exact fun hp => hp ▸ rfl

/--
`SWICat.evalMapApplyPoly x p := (p.map (Pi.ringHom fun _ => C)).eval (fun e => T k e) x`.
-/
noncomputable def evalMapApplyPoly {k : Type*} [Field k] {I : SWICat}
    (x : I.X) (p : MvPolynomial I.E k) :=
  (p.map (Pi.ringHom fun _ => C)).eval (fun e => T k e) x

lemma evalMapApplyPoly_def {k : Type*} [Field k] {I : SWICat}
    (x : I.X) (p : MvPolynomial I.E k) :
  evalMapApplyPoly x p = (p.map (Pi.ringHom fun _ => C)).eval (fun e => T k e) x := rfl

lemma wewew {k : Type*} [Field k] {I : SWICat}
    (x : I.X) (p : MvPolynomial I.E k) :
    (evalMapApplyPoly x p).support ⊆ p.support := by
  intro m hm
  refine mem_support_iff.2 fun hmp => ?_
  · have := eval_map_ringHom_apply_eq_eval_map_C_apply' x p ▸ evalMapApplyPoly_def x p ▸
      mem_support_iff.1 hm
    simp only [T] at this
    sorry

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

lemma bbbbb {k : Type*} [Field k] {i : k} (hi : i ≠ 0) {I : SWICat} (x : I.X)
    {m : I.E →₀ ℕ} {p : MvPolynomial I.E k} (hmp : m ∉ p.support) :
    (((monomial m i + p).map (Pi.ringHom fun x => C)).eval fun e => T k e) x = 0 ↔
      (((monomial m i).map (Pi.ringHom fun x => C)).eval fun e => T k e) x = 0 ∧
      ((p.map (Pi.ringHom fun x => C)).eval fun e => T k e) x = 0 := by
  sorry

-- example (k : Type*) [Field k] {I : SWICat} (p : MvPolynomial { T k e | e : I.E } k) :
--     IsOpen { x : I.X | (p.map (Pi.ringHom fun x => C)).eval (fun s => s.1) x ≠ 0 } ∧
--       IsCompact { x : I.X | (p.map (Pi.ringHom fun x => C)).eval (fun s => s.1) x ≠ 0 } := by
--   refine p.monomial_add_induction_on (fun i => ?_) (fun m i p hmp hi ⟨hp1, hp2⟩ => ?_)
--   · simp only [map_C, eval_C, Pi.ringHom_apply, ne_eq, map_eq_zero, isOpen_const, true_and]
--     by_cases hi : i = 0
--     · simp only [hi, not_true_eq_false, Set.setOf_false, Set.finite_empty, Set.Finite.isCompact]
--     · simp only [hi, not_false_eq_true, Set.setOf_true, isCompact_univ]
--   · simp only [Set.coe_setOf, Set.mem_setOf_eq, map_add, map_monomial, Pi.add_apply, ne_eq]
--     have := Set.notMem_subset (p.support_map_subset (Pi.ringHom fun x : I.X => @C k I.E _)) hmp
--     sorry

lemma aaaaa (k : Type*) [Field k] {I : SWICat} (p : MvPolynomial I.E k) :
    IsOpen { x : I.X | (p.map (Pi.ringHom fun x => C)).eval (fun e => T k e) x ≠ 0 } ∧
      IsCompact { x : I.X | (p.map (Pi.ringHom fun x => C)).eval (fun e => T k e) x ≠ 0 } := by
  refine p.monomial_add_induction_on (fun i => ?_) (fun m i p hmp hi ⟨hp1, hp2⟩ => ?_)
  · simp only [map_C, eval_C, Pi.ringHom_apply, ne_eq, map_eq_zero, isOpen_const, true_and]
    by_cases hi : i = 0
    · simp only [hi, not_true_eq_false, Set.setOf_false, Set.finite_empty, Set.Finite.isCompact]
    · simp only [hi, not_false_eq_true, Set.setOf_true, isCompact_univ]
  · sorry

lemma eeef (k : Type*) [Field k] {I : SWICat} (a : I.X → MvPolynomial I.E k)
    (ha : a ∈ Subring.closure ((Pi.ringHom fun x => C).range.carrier ∪ { T k e | e : I.E })) :
    IsOpen { x : I.X | a x ≠ 0 } ∧ IsCompact { x : I.X | a x ≠ 0 } := by
  obtain ⟨p, hp⟩ := exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure (le_refl _)
    (Set.Subset.refl _) ha
  sorry

open Classical in
lemma springLike' (k : Type*) [Field k] (I : SWICat) :
    SpringLike' (Subring.closure ((Pi.ringHom fun x => C).range.carrier ∪
      { T k e | e : I.E })) where
  spectralSpace := I.spectralSpace
  forall_isOpen := fun a ha => by
    sorry
    -- refine closure_induction (fun a ha => ?_) ?_ ?_ (fun a b _ _ ha hb => ?_) ?_ ?_ ha
    -- · refine ha.elim (fun ⟨i, hai⟩ => hai ▸ ?_) (fun ⟨e, hex⟩ => ?_)
    --   · by_cases hi : i = 0
    --     · exact hi ▸ C_0 (R := k) ▸ (Set.Subset.antisymm (fun _ h _ => h) fun _ h => h rfl) ▸
    --         isOpen_const
    --     · exact (Set.ext fun x => ⟨fun hix => Set.mem_univ x, fun hx => C_ne_zero.2 hi⟩) ▸
    --         isOpen_univ
    --   · exact hex ▸ t_apply_support_eq_g k e ▸ I.forall_isOpen e
    -- · simp only [Pi.zero_apply, ne_eq, not_true_eq_false, Set.setOf_false, isOpen_empty]
    -- · simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true, Set.setOf_true, isOpen_univ]
    -- · sorry
    -- · sorry
    -- · sorry
  forall_isCompact := fun a ha => by
    sorry
    -- refine closure_induction (fun a ha => ?_) ?_ ?_ ?_ ?_ ?_ ha
    -- · refine ha.elim (fun ⟨i, hai⟩ => hai ▸ ?_) (fun ⟨e, hex⟩ => ?_)
    --   · by_cases hi : i = 0
    --     · exact hi ▸ C_0 (R := k) ▸ (Set.Subset.antisymm (fun _ h _ => h) fun _ h => h rfl) ▸
    --         isCompact_empty
    --     · exact (Set.ext fun x => ⟨fun hix => Set.mem_univ x, fun hx => C_ne_zero.2 hi⟩) ▸
    --         isCompact_univ
    --   · exact hex ▸ t_apply_support_eq_g k e ▸ I.forall_isCompact e
    -- · simp only [Pi.zero_apply, ne_eq, not_true_eq_false, Set.setOf_false, isCompact_empty]
    -- · simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true, Set.setOf_true,
    --     isCompact_univ]
    -- · sorry
    -- · sorry
    -- · sorry
  isTopologicalBasis := sorry

end SWICat
