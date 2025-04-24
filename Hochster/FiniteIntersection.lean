import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Compactness.Compact

variable (X : Type*) [TopologicalSpace X]

/--
A collection of closed subsets of `X` has the finite intersection property if every finite
subcollection has nonempty intersection.
-/
structure FiniteInterClosedSet where
  carrier : Set (Set X)
  forall_isClosed : ∀ s : carrier, IsClosed s.1
  finite_inter : ∀ T : Set (Set X), T ⊆ carrier → Nonempty T → Finite T → ⋂ t : T, t.1 ≠ ∅

namespace FiniteInterClosedSet

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

end FiniteInterClosedSet
