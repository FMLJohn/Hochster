import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Defs.Basic

universe u
variable (X : Type u) [TopologicalSpace X]

namespace TopologicalSpace

/--
A cover of a topological space `X` is a collection of subsets of `X` that cover `X`.
-/
structure Cover where
  ι : Type u
  toFun : ι → Set X
  covers : ⋃ i : ι, toFun i = Set.univ

/--
The type of open covers of `X`.
-/
structure OpenCover extends Cover X where
  forall_isOpen : ∀ i : ι, IsOpen (toFun i)

namespace Cover

instance instPreorder : Preorder (Cover X) where
  le := fun U V => { U.toFun i | i : U.ι } ≤ { V.toFun i | i : V.ι }
  lt := fun U V => { U.toFun i | i : U.ι } < { V.toFun i | i : V.ι }
  le_refl := fun _ => fun _ s => s
  le_trans := fun _ _ _ hUV hVW => fun _ s => hVW (hUV s)
  lt_iff_le_not_le := fun _ _ => Eq.to_iff rfl

variable {X} in
/--
Given `U V : Cover X`, `Subcover U V` means that `U` is a subcover of `V`.
-/
def Subcover (U V : Cover X) := U ≤ V

end Cover

/--
The type of covers of `X` with no finite subcover.
-/
structure CoverWithNoFiniteSubcover extends Cover X where
  not_exists : ¬∃ V : Cover X, Finite V.ι ∧ Cover.Subcover V ⟨ι, toFun, covers⟩

instance CoverWithNoFiniteSubcover.instPreorder : Preorder (CoverWithNoFiniteSubcover X) where
  le := fun U V => { U.toFun i | i : U.ι } ≤ { V.toFun i | i : V.ι }
  lt := fun U V => { U.toFun i | i : U.ι } < { V.toFun i | i : V.ι }
  le_refl := fun _ => fun _ s => s
  le_trans := fun _ _ _ hUV hVW => fun _ s => hVW (hUV s)
  lt_iff_le_not_le := fun _ _ => Eq.to_iff rfl

/--
The type of open covers of `X` with no finite subcover.
-/
structure OpenCoverWithNoFiniteSubcover extends OpenCover X where
  not_exists : ¬∃ V : Cover X, Finite V.ι ∧ Cover.Subcover V ⟨ι, toFun, covers⟩

namespace OpenCoverWithNoFiniteSubcover

instance instPreorder : Preorder (OpenCoverWithNoFiniteSubcover X) where
  le := fun U V => { U.toFun i | i : U.ι } ≤ { V.toFun i | i : V.ι }
  lt := fun U V => { U.toFun i | i : U.ι } < { V.toFun i | i : V.ι }
  le_refl := fun _ => fun _ s => s
  le_trans := fun _ _ _ hUV hVW => fun _ s => hVW (hUV s)
  lt_iff_le_not_le := fun _ _ => Eq.to_iff rfl

variable {X}

lemma nonempty_of_not_compactSpace (h : ¬CompactSpace X) :
    Nonempty (OpenCoverWithNoFiniteSubcover X) := by
  have not_isCompact : ¬IsCompact Set.univ := fun c => h ((@isCompact_univ_iff X _).1 c)
  simp only [isCompact_iff_finite_subcover, Set.univ_subset_iff, not_forall] at not_isCompact
  rcases not_isCompact with ⟨ι, toFun, forall_isOpen, covers, not_exists⟩
  constructor; fconstructor
  · exact ⟨⟨ι, toFun, covers⟩, forall_isOpen⟩
  · simp only [_root_.not_exists, not_and]
    intro U hU1 hU2
    change { U.toFun i | i : U.ι } ⊆ { toFun i | i : ι } at hU2
    have forall_exists (i : U.ι) : ∃ j : ι, U.toFun i = toFun j := by
      simp only [Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff] at hU2
      obtain ⟨j, hj⟩ := hU2 i
      use j
      exact hj.symm
    have finite : Finite ((fun i => (forall_exists i).choose) '' ⊤) :=
      Finite.Set.finite_image ⊤ fun i => (forall_exists i).choose
    have : ⋃ i ∈ Set.Finite.toFinset finite, toFun i = Set.univ := by
      rw [← U.covers]
      ext
      simp only [Set.top_eq_univ, Set.image_univ, Set.Finite.mem_toFinset, Set.mem_range,
        Set.iUnion_exists, Set.iUnion_iUnion_eq', Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        use i
        rw [(forall_exists i).choose_spec]
        exact hi
      · rintro ⟨i, hi⟩
        use i
        rw [← (forall_exists i).choose_spec]
        exact hi
    exact not_exists ⟨Set.Finite.toFinset finite, this⟩

lemma isEmpty_of_compactSpace (h : CompactSpace X) :
    IsEmpty (OpenCoverWithNoFiniteSubcover X) := by
  let is_compact : IsCompact ⊤ := (@isCompact_univ_iff X _).2 h
  simp only [isCompact_iff_finite_subcover, Set.top_eq_univ, Set.univ_subset_iff] at is_compact
  constructor
  intro U
  have := is_compact U.toFun U.forall_isOpen U.covers
  refine U.not_exists ⟨?_, ?_⟩
  · exact {
    ι := this.choose
    toFun := fun i => U.toFun i
    covers := by
      have heq : ⋃ i ∈ this.choose, U.toFun i = ⋃ i : { i // i ∈ this.choose }, U.toFun i := by
        ext
        simp only [Set.mem_iUnion, Subtype.exists]
      rw [← heq]
      exact this.choose_spec }
  · constructor
    · exact Finite.of_fintype _
    · intro _ ⟨i, hi⟩
      use i

variable (X) in
lemma isEmpty_iff_compactSpace :
    IsEmpty (OpenCoverWithNoFiniteSubcover X) ↔ CompactSpace X := by
  constructor
  · contrapose
    simp only [not_isEmpty_iff]
    exact fun h ↦ nonempty_of_not_compactSpace h
  · exact fun h ↦ isEmpty_of_compactSpace h

lemma bddAbove_of_isChain [CompactSpace X] (C : Set (OpenCoverWithNoFiniteSubcover X)) :
    IsChain (fun U V => U ≤ V) C → BddAbove C := by
  intro h
  rw [BddAbove]
  fconstructor
  · sorry
  · sorry

end OpenCoverWithNoFiniteSubcover

end TopologicalSpace
