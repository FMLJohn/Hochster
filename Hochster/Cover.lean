import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Defs.Basic

variable (X : Type*) [TopologicalSpace X]

namespace TopologicalSpace

/--
A cover of a topological space `X` is a collection of subsets of `X` that cover `X`.
-/
structure Cover' where
  carrier : Set (Set X)
  covers : ⋃ s : carrier, s.1 = Set.univ

/--
The type of open covers of `X`.
-/
structure OpenCover' extends Cover' X where
  forall_isOpen : ∀ s : carrier, IsOpen s.1

namespace Cover'

instance instSetLike : SetLike (Cover' X) (Set X) where
  coe := fun U => U.carrier
  coe_injective' := by
    intro U V h
    obtain ⟨_, _⟩ := U
    congr

instance instPartialOrder : PartialOrder (Cover' X) := SetLike.instPartialOrder

variable {X} in
/--
Given `U V : Cover' X`, `Subcover' U V` means that `U` is a subcover of `V`.
-/
def Subcover' (U V : Cover' X) := U ≤ V

variable {X} in
/--
Given a collection of covers of `X`, the union of them is again a cover.
-/
def iUnion (S : Set (Cover' X)) [Nonempty S] : Cover' X where
  carrier := ⋃ s : S, s.1
  covers := by
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop, Set.iUnion_exists, Set.biUnion_and']
    have : ⋃ s : (Classical.ofNonempty : S).1.carrier, s ⊆ ⋃ S' ∈ S, ⋃ s ∈ S', s := by
      intro x hx
      simp only [Set.mem_iUnion, exists_prop]
      use (Classical.ofNonempty : S).1
      constructor
      · exact Subtype.coe_prop Classical.ofNonempty
      · simpa only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] using hx
    rw [(Classical.ofNonempty : S).1.2] at this
    exact (Set.Subset.antisymm this fun _ _ ↦ trivial).symm

end Cover'

/--
The type of covers of `X` with no finite subcover.
-/
structure CoverWithNoFiniteSubcover' extends Cover' X where
  not_exists : ¬∃ V : Cover' X, Finite V.carrier ∧ Cover'.Subcover' V ⟨carrier, covers⟩

instance CoverWithNoFiniteSubcover'.instSetLike :
    SetLike (CoverWithNoFiniteSubcover' X) (Set X) where
  coe := fun U => U.carrier
  coe_injective' := by
    intro U V h
    obtain ⟨⟨_, _⟩, _⟩ := U
    congr

instance CoverWithNoFiniteSubcover'.instPartialOrder :
    PartialOrder (CoverWithNoFiniteSubcover' X) := SetLike.instPartialOrder

/--
The type of open covers of `X` with no finite subcover.
-/
structure OpenCoverWithNoFiniteSubcover' extends OpenCover' X, CoverWithNoFiniteSubcover' X where

namespace OpenCoverWithNoFiniteSubcover'

instance instSetLike : SetLike (OpenCoverWithNoFiniteSubcover' X) (Set X) where
  coe := fun U => U.carrier
  coe_injective' := by
    intro U V h
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := U
    congr

instance instPartialOrder : PartialOrder (OpenCoverWithNoFiniteSubcover' X) :=
  SetLike.instPartialOrder

variable {X}

lemma nonempty_of_not_compactSpace (h : ¬CompactSpace X) :
    Nonempty (OpenCoverWithNoFiniteSubcover' X) := by
  have not_isCompact : ¬IsCompact Set.univ := fun c => h ((@isCompact_univ_iff X _).1 c)
  simp only [isCompact_iff_finite_subcover, Set.univ_subset_iff, not_forall] at not_isCompact
  rcases not_isCompact with ⟨ι, toFun, forall_isOpen, covers, not_exists⟩
  constructor; fconstructor
  · fconstructor
    · exact ⟨toFun '' ⊤, by
        refine Eq.trans ?_ covers
        simp only [Set.top_eq_univ, Set.iUnion_coe_set, Set.image_univ, Set.mem_range,
          Set.iUnion_exists, Set.iUnion_iUnion_eq']⟩
    · simpa only [Subtype.forall, Set.top_eq_univ, Set.image_univ, Set.mem_range,
        forall_exists_index, forall_apply_eq_imp_iff] using forall_isOpen
  · simp only [Set.top_eq_univ, Set.image_univ, _root_.not_exists, not_and]
    intro U hU1 hU2
    have forall_exists (s : U.carrier) : ∃ i : ι, toFun i = s := hU2 s.2
    have finite : Finite ((fun s => (forall_exists s).choose) '' ⊤) :=
      Finite.Set.finite_image ⊤ fun s => (forall_exists s).choose
    have : ⋃ i ∈ Set.Finite.toFinset finite, toFun i = Set.univ := by
      rw [← U.covers]
      ext
      simp only [Set.top_eq_univ, Set.image_univ, Set.Finite.mem_toFinset, Set.mem_range,
        Set.iUnion_exists, Set.iUnion_iUnion_eq', Set.mem_iUnion]
      constructor
      · rintro ⟨s, hs⟩
        use s
        rw [← (forall_exists s).choose_spec]
        exact hs
      · rintro ⟨s, hs⟩
        use s
        rw [(forall_exists s).choose_spec]
        exact hs
    exact not_exists ⟨Set.Finite.toFinset finite, this⟩

lemma isEmpty_of_compactSpace (h : CompactSpace X) :
    IsEmpty (OpenCoverWithNoFiniteSubcover' X) := by
  let is_compact : IsCompact ⊤ := (@isCompact_univ_iff X _).2 h
  simp only [isCompact_iff_finite_subcover, Set.top_eq_univ, Set.univ_subset_iff] at is_compact
  constructor
  intro U
  obtain ⟨ι, hι⟩ := is_compact (fun (s : U) => s) U.forall_isOpen U.covers
  refine U.not_exists ⟨?_, ?_⟩
  · exact ⟨(fun i : ι => i) '' ⊤, by
      ext
      simp only [← hι, Set.top_eq_univ, Set.image_univ, Set.mem_range, Subtype.exists, exists_prop,
        exists_and_right, exists_eq_right, Set.mem_iUnion]⟩
  · exact ⟨Finite.Set.finite_image (⊤ : Set ι) (fun i => (@Subtype.val _ (fun s => s ∈ U) i)),
      fun _ ⟨i, hi1, hi2⟩ => by simp only [← hi2, SetLike.coe_mem]⟩

variable (X) in
lemma isEmpty_iff_compactSpace :
    IsEmpty (OpenCoverWithNoFiniteSubcover' X) ↔ CompactSpace X := by
  constructor
  · contrapose
    simp only [not_isEmpty_iff]
    exact fun h ↦ nonempty_of_not_compactSpace h
  · exact fun h ↦ isEmpty_of_compactSpace h

/--
If `X` is nonempty, then given any nonempty chain `C` with elements in
`OpenCoverWithNoFiniteSubcover' X`, the union of elements of `C` forms an open cover of `X` with no
finite subcover.
-/
def chainIUnion [Nonempty X] {C : Set (OpenCoverWithNoFiniteSubcover' X)} [Nonempty C]
    (hC : IsChain (fun U V => U ≤ V) C) : OpenCoverWithNoFiniteSubcover' X where
  carrier := ⋃ s : C, s.1.carrier
  covers := by
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop, Set.iUnion_exists, Set.biUnion_and']
    have : ⋃ s : (Classical.ofNonempty : C).1.carrier, s ⊆ ⋃ S' ∈ C, ⋃ s ∈ S', s := by
      intro x hx
      simp only [Set.mem_iUnion, exists_prop]
      use (Classical.ofNonempty : C).1
      constructor
      · exact Subtype.coe_prop Classical.ofNonempty
      · simpa only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] using hx
    rw [(Classical.ofNonempty : C).1.1.1.2] at this
    exact (Set.Subset.antisymm this fun _ _ => trivial).symm
  forall_isOpen := by
    rintro ⟨O, hO⟩
    simp only [Set.iUnion_coe_set, Set.mem_iUnion] at hO
    exact Subtype.forall.1 hO.choose.1.2 O hO.choose_spec.2
  not_exists := by
    by_contra h
    obtain ⟨V, hV1, hV2⟩ := h
    simp only [Cover'.Subcover', Set.iUnion_coe_set] at hV2
    haveI : Nonempty V.carrier := by
      by_contra h
      simp only [not_nonempty_iff] at h
      let hV := V.covers
      simp only [Set.iUnion_of_empty] at hV
      exact (not_nonempty_iff.mpr <| Set.univ_eq_empty_iff.mp hV.symm) inferInstance
    sorry

end OpenCoverWithNoFiniteSubcover'

end TopologicalSpace
