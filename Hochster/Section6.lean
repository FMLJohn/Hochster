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

lemma t_apply_support_eq_g (k : Type*) [Field k] {I : SWICat} (e : I.E) :
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

/--
`Subring.repMvPoly' hr = (Subring.exists_mvPolynomial_of_mem_closure' hr).choose`.
-/
noncomputable def repMvPoly' {R : Type*} [CommRing R] {A : Subring R}
    {S : Set R} {r : R} (hr : r ∈ closure (A.carrier ∪ S)) :=
  (exists_mvPolynomial_of_mem_closure' hr).choose

lemma map_repMvPoly'_eval_eq {R : Type*} [CommRing R] {A : Subring R}
    {S : Set R} {r : R} (hr : r ∈ closure (A.carrier ∪ S)) :
    ((repMvPoly' hr).map A.subtype).eval (fun s : S => s.1) = r :=
  (exists_mvPolynomial_of_mem_closure' hr).choose_spec

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

/--
Given any `α : Type*`, ring `R` and `S : Subring R`,
`(S.funcConst α).carrier := { fun _ => s | s ∈ S }`.
-/
def funcConst (α : Type*) {R : Type*} [Ring R] (S : Subring R) :
    Subring (α → R) where
  carrier := { fun _ => s | s ∈ S }
  mul_mem' := fun ⟨s, hsS, hs⟩ ⟨t, htS, ht⟩ => ⟨s * t, S.mul_mem hsS htS, hs ▸ ht ▸ rfl⟩
  one_mem' := ⟨1, S.one_mem, rfl⟩
  add_mem' := fun ⟨s, hsS, hs⟩ ⟨t, htS, ht⟩ => ⟨s + t, S.add_mem hsS htS, hs ▸ ht ▸ rfl⟩
  zero_mem' := ⟨0, S.zero_mem, rfl⟩
  neg_mem' := fun ⟨s, hsS, hs⟩ => ⟨-s, S.neg_mem hsS, hs ▸ rfl⟩

end Subring

namespace SWICat

lemma wewfw (k : Type*) [Field k] {I : SWICat}
    {p : MvPolynomial { T k e | e : I.E } ((@C k I.E _).range.funcConst I.X)} :
    IsOpen { x : I.X | ((p.map ((@C k I.E _).range.funcConst I.X).subtype).eval
      fun s => s.1) x ≠ 0 } ∧
        IsCompact { x : I.X | ((p.map ((@C k I.E _).range.funcConst I.X).subtype).eval
          fun s => s.1) x ≠ 0 } := by
  refine p.monomial_add_induction_on (fun ⟨a, i, _, hai⟩ => ?_)
    (fun m ⟨a, p, ⟨i, hip⟩, hap⟩ q hmq ha ⟨hqX1, hqX2⟩ => ?_)
  · simp only [← hai, map_C, subtype_apply, eval_C, ne_eq, isOpen_const, true_and]
    by_cases hi : i = 0
    · simp only [hi, not_true_eq_false, Set.setOf_false, Set.finite_empty, Set.Finite.isCompact]
    · simp only [hi, not_false_eq_true, Set.setOf_true, isCompact_univ]
  · refine (MvPolynomial.map (funcConst I.X (@C k I.E _).range).subtype).map_add .. ▸ ⟨?_, ?_⟩
    · sorry
    · sorry

lemma eeef (k : Type*) [Field k] {I : SWICat} (a : I.X → MvPolynomial I.E k)
    (ha : a ∈ Subring.closure ((MvPolynomial.C.range.funcConst I.X).carrier ∪
    { T k e | e : I.E })) :
    IsOpen { x : I.X | a x ≠ 0 } ∧ IsCompact { x : I.X | a x ≠ 0 } := by
  obtain ⟨p, hp⟩ := exists_mvPolynomial_of_mem_closure ha
  sorry



open Classical in
lemma springLike' (k : Type*) [Field k] (I : SWICat) :
    SpringLike' (Subring.closure ((MvPolynomial.C.range.funcConst I.X).carrier ∪
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
