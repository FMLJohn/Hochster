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

open Classical in
lemma springLike' (k : Type*) [Field k] (I : SWICat) :
    SpringLike' (Subring.closure ({ fun x => MvPolynomial.C i | i : k } ∪
      { T k e | e : I.E })) where
  spectralSpace := I.spectralSpace
  forall_isOpen := fun a ha => by
    refine closure_induction (fun a ha => ?_) ?_ ?_ (fun a b _ _ ha hb => ?_) ?_ ?_ ha
    · refine ha.elim (fun ⟨i, hai⟩ => hai ▸ ?_) (fun ⟨e, hex⟩ => ?_)
      · by_cases hi : i = 0
        · exact hi ▸ C_0 (R := k) ▸ (Set.Subset.antisymm (fun _ h _ => h) fun _ h => h rfl) ▸
            isOpen_const
        · exact (Set.ext fun x => ⟨fun hix => Set.mem_univ x, fun hx => C_ne_zero.2 hi⟩) ▸
            isOpen_univ
      · exact hex ▸ t_apply_support_eq_g k e ▸ I.forall_isOpen e
    · simp only [Pi.zero_apply, ne_eq, not_true_eq_false, Set.setOf_false, isOpen_empty]
    · simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true, Set.setOf_true, isOpen_univ]
    · sorry
    · sorry
    · sorry
  forall_isCompact := fun a ha => by
    refine closure_induction (fun a ha => ?_) ?_ ?_ ?_ ?_ ?_ ha
    · refine ha.elim (fun ⟨i, hai⟩ => hai ▸ ?_) (fun ⟨e, hex⟩ => ?_)
      · by_cases hi : i = 0
        · exact hi ▸ C_0 (R := k) ▸ (Set.Subset.antisymm (fun _ h _ => h) fun _ h => h rfl) ▸
            isCompact_empty
        · exact (Set.ext fun x => ⟨fun hix => Set.mem_univ x, fun hx => C_ne_zero.2 hi⟩) ▸
            isCompact_univ
      · exact hex ▸ t_apply_support_eq_g k e ▸ I.forall_isCompact e
    · simp only [Pi.zero_apply, ne_eq, not_true_eq_false, Set.setOf_false, isCompact_empty]
    · simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true, Set.setOf_true,
        isCompact_univ]
    · sorry
    · sorry
    · sorry
  isTopologicalBasis := sorry

end SWICat
