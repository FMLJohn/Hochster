import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Compactness.Compact

variable (X : Type*) [TopologicalSpace X]

/--
A collection of closed subsets of `X` such that every nonempty finite subcollection has nonempty
intersection.
-/
structure FiniteInterClosedSet where
  carrier : Set (Set X)
  forall_isClosed : ∀ s : carrier, IsClosed s.1
  finite_inter : ∀ T : Set (Set X), T ⊆ carrier → Nonempty T → Finite T → ⋂ t : T, t.1 ≠ ∅

namespace FiniteInterClosedSet

lemma forall_of_CompactSpace [Nonempty X] :
    CompactSpace X → ∀ U : FiniteInterClosedSet X, ⋂ s : U.carrier, s.1 ≠ ∅ := by
  intro h U empty
  have forall_isOpen (s : U.carrier) : IsOpen s.1ᶜ :=
    @IsClosed.isOpen_compl _ _ _ <| U.forall_isClosed s
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
    simp only [Set.mem_range, Subtype.exists, exists_prop, exists_and_right, exists_eq_right] at hs
    exact hs.choose
  have eq : ⋃ s ∈ t, s.1ᶜ = ⋃ s : (Set.range (fun (s : t) => s.1.1)), s.1ᶜ := by
    simp only [Set.iUnion_coe_set, exists_prop, exists_and_right, Set.mem_range, Subtype.exists,
      exists_eq_right, Set.iUnion_exists]
  rw [eq, ← Set.compl_iInter, Set.compl_eq_univ_diff, sdiff_eq_left, Set.univ_disjoint] at ht
  exact U.finite_inter (Set.range (fun (s : t) => s.1.1)) subset nonempty (Set.finite_range _) ht

lemma CompactSpace_of_forall :
    (∀ U : FiniteInterClosedSet X, ⋂ s : U.carrier, s.1 ≠ ∅) → CompactSpace X := by
  intro h
  constructor
  · by_contra not_compact
    simp only [isCompact_iff_finite_subfamily_closed, Set.univ_inter, not_forall, Classical.not_imp,
      not_exists] at not_compact
    rcases not_compact with ⟨ι, U, forall_isClosed, empty, forall_not_eq⟩
    let fics : FiniteInterClosedSet X := {
      carrier := Set.range U
      forall_isClosed := by
        intro s
        obtain ⟨i, hi⟩ := Set.mem_range.1 s.2
        simpa only [hi] using forall_isClosed i
      finite_inter := by
        intro T hT1 hT2 hT3
        have forall_exists (s : T) : ∃ i : ι, U i = s := hT1 s.2
        let t := Set.Finite.toFinset <| Finite.Set.finite_range fun s => (forall_exists s).choose
        have neq := forall_not_eq t
        have eq : ⋂ i ∈ t, U i = ⋂ s : T, s.1 := by
          ext
          simp only [t, Set.mem_iInter, Set.iInter_coe_set, Set.Finite.mem_toFinset, Set.mem_range,
            Subtype.exists, forall_exists_index]
          constructor
          · intro forall_imp s hsT
            simpa only [(forall_exists ⟨s, hsT⟩).choose_spec]
              using forall_imp (forall_exists ⟨s, hsT⟩).choose s hsT rfl
          · intro forall_mem i s hsT eq
            simpa only [← eq, (forall_exists ⟨s, hsT⟩).choose_spec] using forall_mem s hsT
        simpa only [eq] using neq }
    exact h fics <| by simpa only [fics, Set.iInter_coe_set, Set.mem_range, Set.iInter_exists,
      Set.iInter_iInter_eq'] using empty

lemma CompactSpace_iff_forall [Nonempty X] :
    CompactSpace X ↔ ∀ U : FiniteInterClosedSet X, ⋂ s : U.carrier, s.1 ≠ ∅ :=
  ⟨forall_of_CompactSpace X, CompactSpace_of_forall X⟩

instance instSetLike : SetLike (FiniteInterClosedSet X) (Set X) where
  coe := fun U => U.carrier
  coe_injective' := by
    intro U V h
    obtain ⟨_, _⟩ := U
    congr

instance instPreorder : PartialOrder (FiniteInterClosedSet X) := SetLike.instPartialOrder

open Classical

variable {X}

/-- `(chainIUnion hC).carrier := ⋃ U : C, U.1.1`. -/
def chainIUnion {C : Set (FiniteInterClosedSet X)} (hC : IsChain (fun U V => U ≤ V) C) :
    FiniteInterClosedSet X where
  carrier := ⋃ U : C, U.1.1
  forall_isClosed := by
    rintro ⟨s, S, hS, hsS⟩
    simp only [Set.mem_range, Subtype.exists] at hS
    rcases hS with ⟨U, hU1, hU2⟩
    exact U.forall_isClosed ⟨s, show s ∈ U.carrier by simpa only [hU2] using hsS⟩
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

lemma le_chainIUnion {C : Set (FiniteInterClosedSet X)}
    (hC : IsChain (fun U V => U ≤ V) C) (U : C) : U.1 ≤ chainIUnion hC :=
  fun _ h => ⟨U, ⟨U, rfl⟩, h⟩

lemma exists_le_isMax (U : FiniteInterClosedSet X) :
    ∃ V : FiniteInterClosedSet X, U ≤ V ∧ IsMax V := by
  refine zorn_le_nonempty_Ici₀ U ?_ U (fun _ h => h)
  · intro C _ hC _ _
    use chainIUnion hC
    intro U' hU'
    exact le_chainIUnion hC ⟨U', hU'⟩

lemma CompactSpace_of_forall_isMax_neq :
    (∀ U : FiniteInterClosedSet X, IsMax U → ⋂ s : U.carrier, s.1 ≠ ∅) → CompactSpace X := by
  intro h
  refine CompactSpace_of_forall X ?_
  · intro U heq
    obtain ⟨V, hV1, hV2⟩ := exists_le_isMax U
    have : ⋂ s : V.carrier, s.1 ⊆ ⋂ s : U.carrier, s.1 := by
      intro x
      simp only [Set.iInter_coe_set, Set.mem_iInter]
      intro hx s hs
      exact hx s (hV1 hs)
    simp only [heq, Set.subset_empty_iff] at this
    exact h V hV2 this

lemma CompactSpace_iff_forall_isMax_neq [Nonempty X] :
    CompactSpace X ↔ (∀ U : FiniteInterClosedSet X, IsMax U → ⋂ s : U.carrier, s.1 ≠ ∅) :=
  ⟨fun h U _ => forall_of_CompactSpace X h U, CompactSpace_of_forall_isMax_neq⟩

end FiniteInterClosedSet
