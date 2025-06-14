import Hochster.Section2Complicated.AlexanderSubbasis.IntersectionCover

open TopologicalSpace

universe u
variable {X ι : Type u} [T : TopologicalSpace X] {U : ι → Set X}
variable (hTU : T = generateFrom (U '' ⊤))

include hTU in
theorem alexanderSubbasis :
    (∀ s : Set ι, (⋃ i : s, U i = ⊤ → ∃ t : Finset s, ⋃ i : t, U i = ⊤)) →
    CompactSpace X := by
  intro hι
  by_cases h1 : IsEmpty X
  · exact Finite.compactSpace
  · simp only [not_isEmpty_iff] at h1
    by_contra h
    let s : Set ι := { i | U i ∈ (IntersectionCover h hTU).toFun '' ⊤ }
    have covers : ⋃ i : s, U i = ⊤ := by
      ext x
      have mem : x ∈ ⋃ i, (IntersectionCover h hTU).toFun i := by
        rw [(IntersectionCover h hTU).covers]
        exact trivial
      simp only [s, Set.top_eq_univ, Set.coe_setOf, Set.mem_iUnion, Subtype.exists, Set.image_univ,
        Set.mem_range, exists_prop, Set.mem_univ, iff_true, IntersectionCover, exists_eq_right]
        at mem ⊢
      rcases mem with ⟨O, hO1, hO2⟩
      use (Set.mem_range.1 <| Set.mem_of_mem_inter_left hO1).choose
      rw [(Set.mem_range.1 <| Set.mem_of_mem_inter_left hO1).choose_spec]
      exact ⟨hO1, hO2⟩
    let cover : Cover X := {
      ι := (hι s covers).choose
      toFun := fun i => U i
      covers := (hι s covers).choose_spec }
    have subcover : cover.Subcover (OpenCoverWithNoFiniteSubcover.Max h).1.1 := by
      change { cover.toFun i | i : cover.ι } ⊆ _
      simp only [cover, s, IntersectionCover, Set.top_eq_univ, Subtype.exists, Set.image_univ,
        Subtype.range_coe_subtype, Set.setOf_subset_setOf, forall_exists_index, and_imp]
      intro O _ hxi _ hUiO
      rcases hxi with ⟨_, j, hj⟩
      exact ⟨j, hj.trans hUiO⟩
    exact (OpenCoverWithNoFiniteSubcover.Max h).not_exists
      ⟨cover, Finite.of_fintype cover.ι, subcover⟩

include hTU in
theorem alexanderSubbasis_backward_direction :
    CompactSpace X → ∀ s : Set ι, ⋃ i : s, U i = ⊤ → ∃ t : Finset s, ⋃ i : t, U i = ⊤ := by
  intro compact s eq_top
  have forall_isOpen (i : s) : IsOpen (U i) := by
    rw [hTU]
    exact TopologicalSpace.isOpen_generateFrom_of_mem <| Set.mem_image_of_mem U trivial
  let imp := isCompact_iff_finite_subcover.1 CompactSpace.isCompact_univ (fun i : s => U i)
    forall_isOpen
  simpa only [Set.univ_subset_iff, Set.iUnion_subtype] using imp (Set.univ_subset_iff.mpr eq_top)

include hTU in
theorem alexanderSubbasis_iff :
    CompactSpace X ↔ ∀ s : Set ι, ⋃ i : s, U i = ⊤ → ∃ t : Finset s, ⋃ i : t, U i = ⊤ :=
  ⟨alexanderSubbasis_backward_direction hTU, alexanderSubbasis hTU⟩

theorem alexanderSubbasis_closed_version {V : ι → Set X}
    (hTV : T = generateFrom { (V i)ᶜ | i : ι }) :
    (∀ s : Set ι, (⋂ i : s, V i = ∅ → ∃ t : Finset s, ⋂ i : t, V i = ∅)) →
    CompactSpace X := by
  intro hι
  have heq : T = generateFrom ((fun i => (V i)ᶜ) '' ⊤) := by
    simpa only [Set.top_eq_univ, Set.image_univ] using hTV
  refine alexanderSubbasis heq ?_
  · intro s hs
    simp only [← Set.compl_iInter, Set.top_eq_univ, Set.compl_univ_iff] at hs ⊢
    obtain ⟨t, ht⟩ := hι s hs
    use t

theorem aS_closed_backward_direction {V : ι → Set X}
    (hTV : T = generateFrom { (V i)ᶜ | i : ι }) :
    CompactSpace X → (∀ s : Set ι, (⋂ i : s, V i = ∅ → ∃ t : Finset s, ⋂ i : t, V i = ∅)) := by
  intro compact s empty
  have forall_isClosed (i : s) : IsClosed (V i) := by
    have : (V i)ᶜ ∈ { (V i)ᶜ | i : ι } := by use i
    have := TopologicalSpace.isOpen_generateFrom_of_mem this
    simpa only [isOpen_compl_iff, hTV] using this
  have imp := isCompact_iff_finite_subfamily_closed.1 CompactSpace.isCompact_univ
    (fun (i : s) => V i) forall_isClosed
  simp only [Set.univ_inter] at imp
  simpa only [Set.univ_inter, Set.iInter_subtype] using imp empty

theorem AlexanderSubbasis_closed_iff {V : ι → Set X}
    (hTV : T = generateFrom { (V i)ᶜ | i : ι }) :
    CompactSpace X ↔ (∀ s : Set ι, (⋂ i : s, V i = ∅ → ∃ t : Finset s, ⋂ i : t, V i = ∅)) :=
  ⟨aS_closed_backward_direction hTV, alexanderSubbasis_closed_version hTV⟩
