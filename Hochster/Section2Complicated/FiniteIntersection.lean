import Hochster.Section2Complicated.AlexanderSubbasis.Theorem

open TopologicalSpace

universe u
variable {X ι : Type u} [T : TopologicalSpace X] (V : ι → Set X)
variable (hTV : T = generateFrom { (V i)ᶜ | i : ι })

/--
A collection of closed subsets of `X` from `{ (V i)ᶜ | i : ι }` such that every nonempty finite
subcollection has nonempty intersection.
-/
structure FiniteInterClosedSubbasisSet where
  carrier : Set (Set X)
  forall_mem : ∀ s : carrier, s.1 ∈ { V i | i : ι }
  finite_inter : ∀ T : Set (Set X), T ⊆ carrier → Nonempty T → Finite T → ⋂ t : T, t.1 ≠ ∅

namespace FiniteInterClosedSubbasisSet

variable {V}

include hTV in
lemma forall_of_CompactSpace [Nonempty X] :
    CompactSpace X → ∀ U : FiniteInterClosedSubbasisSet V, ⋂ s : U.carrier, s.1 ≠ ∅ := by
  intro h U empty
  have := (@alexanderSubbasis_iff X ι T (fun i => (V i)ᶜ) ?_).1 h
  · have forall_isOpen (s : U.carrier) : IsOpen s.1ᶜ := by
      refine @IsClosed.isOpen_compl _ _ _ ?_
      obtain ⟨i, hi⟩ := U.forall_mem s
      have : (V i)ᶜ ∈ { (V i)ᶜ | i : ι } := by simp only [Set.mem_setOf_eq, exists_apply_eq_apply]
      simpa only [← hi, isOpen_compl_iff, hTV] using isOpen_generateFrom_of_mem this
    have eq_top : ⋃ s : U.carrier, s.1ᶜ = ⊤ := by
      rw [← Set.compl_iInter fun s : U.carrier => s.1]
      exact compl_eq_top.mpr empty
    have exists_subset := @isCompact_iff_finite_subcover.1 (@isCompact_univ X _ h) U.carrier
      (fun s => s.1ᶜ) forall_isOpen (Set.univ_subset_iff.2 eq_top)
    simp only [Set.univ_subset_iff] at exists_subset
    obtain ⟨t, ht⟩ := exists_subset
    have nonempty : Nonempty (Set.range (fun (s : t) => s.1.1)) := by
      have : Nonempty t := by
        by_contra h
        haveI : IsEmpty t := not_nonempty_iff.mp h
        have : ⋃ s ∈ t, s.1ᶜ = ⋃ s : t, s.1.1ᶜ := by
          ext x
          constructor
          · intro hx
            simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop, exists_and_right] at hx ⊢
            obtain ⟨s, ⟨hsU, hst⟩, hxs⟩ := hx
            use ⟨⟨s, hsU⟩, hst⟩
          · intro hx
            simp only [Set.iUnion_of_empty, Set.mem_empty_iff_false] at hx
        simp only [this, Set.iUnion_of_empty] at ht
        exact (not_nonempty_iff.2 <| Set.univ_eq_empty_iff.mp ht.symm) inferInstance
      exact Set.Nonempty.to_subtype <| @Set.range_nonempty _ _ this (fun (s : t) => s.1.1)
    have subset : Set.range (fun (s : t) => s.1.1) ⊆ U.carrier := by
      intro s hs
      simp only [Set.mem_range, Subtype.exists, exists_prop, exists_and_right, exists_eq_right]
        at hs
      exact hs.choose
    have eq : ⋃ s ∈ t, s.1ᶜ = ⋃ s : (Set.range (fun (s : t) => s.1.1)), s.1ᶜ := by
      simp only [Set.iUnion_coe_set, exists_prop, exists_and_right, Set.mem_range, Subtype.exists,
        exists_eq_right, Set.iUnion_exists]
    rw [eq, ← Set.compl_iInter, Set.compl_eq_univ_diff, sdiff_eq_left, Set.univ_disjoint] at ht
    exact U.finite_inter (Set.range (fun (s : t) => s.1.1)) subset nonempty (Set.finite_range _) ht
  · refine Eq.trans hTV ?_
    · ext
      simp only [Set.top_eq_univ, Set.image_univ]

include hTV in
lemma CompactSpace_of_forall :
    (∀ U : FiniteInterClosedSubbasisSet V, ⋂ s : U.carrier, s.1 ≠ ∅) → CompactSpace X := by
  intro h
  by_contra not_compact
  simp only [@AlexanderSubbasis_closed_iff X ι T V hTV, not_forall, not_exists] at not_compact
  rcases not_compact with ⟨s, empty, forall_not⟩
  let ficss : FiniteInterClosedSubbasisSet V := {
    carrier := Set.range fun i : s => V i
    forall_mem := by
      intro s
      obtain ⟨i, hi⟩ := Set.mem_range.1 s.2
      simp only [← hi, Set.mem_setOf_eq, exists_apply_eq_apply]
    finite_inter := by
      intro T hT1 hT2 hT3
      have forall_exists (t : T) : ∃ i : s, V i.1 = t := hT1 t.2
      let t := Set.Finite.toFinset <| Finite.Set.finite_range fun s => (forall_exists s).choose
      have eq : ⋂ i : t, V i = ⋂ s : T, s.1 := by
        ext
        simp only [Set.mem_iInter, Subtype.forall, Set.Finite.mem_toFinset, Set.mem_range,
          Subtype.exists, forall_exists_index, t]
        constructor
        · intro forall_imp s hsT
          simpa only [t, (forall_exists ⟨s, hsT⟩).choose_spec] using
            forall_imp (forall_exists ⟨s, hsT⟩).choose (Subtype.coe_prop
              (forall_exists ⟨s, hsT⟩).choose) s hsT rfl
        · intro forall_mem i his r mem eq
          have : i = (forall_exists ⟨r, mem⟩).choose := (Subtype.ext_iff.1 eq).symm
          rw [this, (forall_exists ⟨r, mem⟩).choose_spec]
          exact forall_mem r mem
      rw [← eq]
      exact forall_not t }
  refine h ficss ?_
  · simpa only [ficss, Set.iInter_coe_set, Set.mem_range, Subtype.exists, exists_prop,
      Set.iInter_exists, Set.biInter_and', Set.iInter_iInter_eq_right] using empty

include hTV in
lemma CompactSpace_iff_forall [Nonempty X] :
    CompactSpace X ↔ ∀ U : FiniteInterClosedSubbasisSet V, ⋂ s : U.carrier, s.1 ≠ ∅ :=
  ⟨forall_of_CompactSpace hTV, CompactSpace_of_forall hTV⟩

instance instSetLike : SetLike (FiniteInterClosedSubbasisSet V) (Set X) where
  coe := fun U => U.carrier
  coe_injective' := by
    intro U V h
    obtain ⟨_, _⟩ := U
    congr

instance instPreorder : PartialOrder (FiniteInterClosedSubbasisSet V) := SetLike.instPartialOrder

open Classical

/-- `(chainIUnion hC).carrier := ⋃ U : C, U.1.1`. -/
def chainIUnion {C : Set (FiniteInterClosedSubbasisSet V)} (hC : IsChain (fun U V => U ≤ V) C) :
    FiniteInterClosedSubbasisSet V where
  carrier := ⋃ U : C, U.1.1
  forall_mem := by
    rintro ⟨s, S, hS, hsS⟩
    simp only [Set.mem_range, Subtype.exists] at hS
    rcases hS with ⟨U, hU1, hU2⟩
    exact U.forall_mem ⟨s, show s ∈ U.carrier by simpa only [hU2] using hsS⟩
  finite_inter := by
    intro T hT1 hT2 hT3 empty
    have forall_exists (t : T) : ∃ U : C, t.1 ∈ U.1.carrier := Set.mem_iUnion.mp (hT1 t.2)
    have exists_isMax : ∃ m : (fun (t : T) => (forall_exists t).choose) '' ⊤, IsMax m := by
      by_contra h
      simp only [not_exists, not_isMax_iff] at h
      haveI : Infinite ((fun (t : T) => (forall_exists t).choose) '' ⊤) :=
        @NoMaxOrder.infinite _ _ (Set.instNonemptyElemImage _ ⊤) ⟨fun U => h U⟩
      exact not_finite ((fun (t : T) => (forall_exists t).choose) '' ⊤)
    have forall_mem (t : T) : t.1 ∈ exists_isMax.choose.1.1.carrier := by
      have : (forall_exists t).choose ≤ exists_isMax.choose.1.1 := by
        by_cases le : exists_isMax.choose ≤ (forall_exists t).choose
        · have := exists_isMax.choose_spec
          simp only [IsMax, Subtype.forall] at this
          exact this (forall_exists t).choose (forall_exists t).choose.coe_prop
            (Set.mem_image_of_mem _ trivial) le
        · have : exists_isMax.choose.1.1 ∈ C := by
            have := exists_isMax.choose.2
            simp only [Set.top_eq_univ, Set.image_univ] at this
            obtain ⟨s, hs⟩ := this
            rw [← hs]
            exact (forall_exists s).choose.coe_prop
          exact Decidable.or_iff_not_imp_right.1
            (IsChain.total hC (forall_exists t).choose.coe_prop this) le
      exact this (forall_exists t).choose_spec
    exact exists_isMax.choose.1.1.finite_inter T (fun t ht => forall_mem ⟨t, ht⟩) hT2 hT3 empty

omit T in
lemma le_chainIUnion {C : Set (FiniteInterClosedSubbasisSet V)}
    (hC : IsChain (fun U V => U ≤ V) C) (U : C) : U.1 ≤ chainIUnion hC :=
  fun _ h => ⟨U, ⟨U, rfl⟩, h⟩

omit T in
lemma exists_le_isMax (U : FiniteInterClosedSubbasisSet V) :
    ∃ V : FiniteInterClosedSubbasisSet V, U ≤ V ∧ IsMax V := by
  refine zorn_le_nonempty_Ici₀ U ?_ U (fun _ h => h)
  · intro C _ hC _ _
    use chainIUnion hC
    intro U' hU'
    exact le_chainIUnion hC ⟨U', hU'⟩

include hTV in
lemma CompactSpace_of_forall_isMax_neq :
    (∀ U : FiniteInterClosedSubbasisSet V, IsMax U → ⋂ s : U.carrier, s.1 ≠ ∅) →
    CompactSpace X := by
  intro h
  refine CompactSpace_of_forall hTV ?_
  · intro U heq
    obtain ⟨V, hV1, hV2⟩ := exists_le_isMax U
    have : ⋂ s : V.carrier, s.1 ⊆ ⋂ s : U.carrier, s.1 := by
      intro x
      simp only [Set.iInter_coe_set, Set.mem_iInter]
      intro hx s hs
      exact hx s (hV1 hs)
    simp only [heq, Set.subset_empty_iff] at this
    exact h V hV2 this

include hTV in
lemma CompactSpace_iff_forall_isMax_neq [Nonempty X] :
    CompactSpace X ↔ (∀ U : FiniteInterClosedSubbasisSet V, IsMax U → ⋂ s : U.carrier, s.1 ≠ ∅) :=
  ⟨fun h U _ => forall_of_CompactSpace hTV h U, CompactSpace_of_forall_isMax_neq hTV⟩

end FiniteInterClosedSubbasisSet
