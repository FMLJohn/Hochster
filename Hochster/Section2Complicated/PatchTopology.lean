import Mathlib.Topology.Spectral.Basic

import Hochster.Section2Complicated.InterOfClosedSets

open Classical FiniteInterClosedSubbasisSet InterOfClosedSets TopologicalSpace Topology

variable (X : Type*) [T : TopologicalSpace X]

/--
The patch topology on a topological space `X` is generated by the open compact subsets of `X` and
the complements of them.
-/
def PatchTopology' : TopologicalSpace X :=
  generateFrom ({ S : Set X | IsOpen S ∧ IsCompact S } ∪
    { S : Set X | ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ S = Oᶜ })

namespace PatchTopology'

lemma t2Space_of_spectralSpace [SpectralSpace X] : @T2Space X (PatchTopology' X) := by
  simp only [t2Space_iff, exists_and_left]
  intro x y hxy
  obtain ⟨s, hs1, hs2⟩ := not_inseparable_iff_exists_open.1 <| (Decidable.not_imp_not.2 <|
    (t0Space_iff_inseparable X).1 inferInstance x y) hxy
  refine Or.elim hs2 ?_ ?_
  · rintro ⟨hxs, hys⟩
    obtain ⟨t, ⟨ht1, ht2⟩, ht3, ht4⟩ := (IsTopologicalBasis.mem_nhds_iff <|
      (prespectralSpace_iff X).1 inferInstance).1 <| IsOpen.mem_nhds hs1 hxs
    use t
    constructor
    · exact isOpen_generateFrom_of_mem <| Set.mem_union_left _ ⟨ht1, ht2⟩
    · use tᶜ
      constructor
      · exact isOpen_generateFrom_of_mem <| Set.mem_union_right _ <| by use t
      · constructor
        · exact ht3
        · exact ⟨fun h => hys (ht4 h), Set.disjoint_compl_right_iff_subset.mpr fun _ h => h⟩
  · rintro ⟨hys, hxs⟩
    obtain ⟨t, ⟨ht1, ht2⟩, ht3, ht4⟩ := (IsTopologicalBasis.mem_nhds_iff <|
      (prespectralSpace_iff X).1 inferInstance).1 <| IsOpen.mem_nhds hs1 hys
    use tᶜ
    constructor
    · exact isOpen_generateFrom_of_mem <| Set.mem_union_right _ <| by use t
    · use t
      constructor
      · exact isOpen_generateFrom_of_mem <| Set.mem_union_left _ ⟨ht1, ht2⟩
      · constructor
        · exact fun h => hxs (ht4 h)
        · exact ⟨ht3, Set.disjoint_compl_left_iff_subset.mpr fun _ h => h⟩

lemma eq_generateFrom_of_SpectralSpace [spectral : SpectralSpace X] :
    PatchTopology' X = generateFrom
      { S : Set X | ∃ C : Set X, (IsClosed C ∨ IsOpen C ∧ IsCompact C) ∧ Cᶜ = S } := by
  refine eq_of_le_of_ge ?_ ?_
  · refine le_generateFrom_iff_subset_isOpen.2 ?_
    · simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro S hS
      refine Or.elim hS ?_ ?_
      · have le : generateFrom ({ S : Set X | IsOpen S ∧ IsCompact S} ∪
            { S : Set X | ∃ O : Set X, IsOpen O ∧ IsCompact O ∧ S = Oᶜ }) ≤ T := by
          rw [spectral.isTopologicalBasis.eq_generateFrom]
          refine le_generateFrom_iff_subset_isOpen.2 ?_
          · simp only [Set.setOf_subset_setOf, and_imp,
              ← spectral.isTopologicalBasis.eq_generateFrom]
            intro S hS1 hS2
            exact isOpen_generateFrom_of_mem <| Or.intro_left _ ⟨hS1, hS2⟩
        exact fun _ => le Sᶜ IsClosed.isOpen_compl
      · rintro ⟨hS1, hS2⟩
        refine isOpen_generateFrom_of_mem ?_
        · simp only [Set.mem_union, Set.mem_setOf_eq, compl_inj_iff, exists_eq_right_right']
          exact Or.intro_right _ ⟨hS1, hS2⟩
  · refine le_generateFrom_iff_subset_isOpen.2 ?_
    · intro S hS
      refine Or.elim hS ?_ ?_
      · rintro ⟨hS1, hS2⟩
        exact isOpen_generateFrom_of_mem ⟨Sᶜ, Or.intro_left _ <| isClosed_compl_iff.mpr hS1,
          compl_compl S⟩
      · rintro ⟨O, hO1, hO2, hO3⟩
        exact isOpen_generateFrom_of_mem ⟨O, Or.intro_right _ ⟨hO1, hO2⟩, hO3.symm⟩

lemma compactSpace_of_spectralSpace [SpectralSpace X] : @CompactSpace X (PatchTopology' X) := by
  by_cases h : Nonempty X
  · let ι := { S : Set X | IsClosed S } ∪ { S : Set X | IsOpen S ∧ IsCompact S }
    let V := fun i : ι => i.1
    have hV : { V i | i : ι } = { S | IsClosed S } ∪ { S | IsOpen S ∧ IsCompact S } := by
      simp only [V, ι, Subtype.exists, exists_prop, exists_eq_right]
      rfl
    have eq : PatchTopology' X = generateFrom { (V i)ᶜ | i : ι } := by
      simp only [ι, V, Subtype.exists, exists_prop]
      exact eq_generateFrom_of_SpectralSpace X
    rw [@CompactSpace_iff_forall_isMax_neq X ι (PatchTopology' X) V eq]
    intro U hU
    obtain ⟨x, hx⟩ := (quasiSober_iff X).1 inferInstance (isIrreducible hV hU) (isClosed U)
    have mem : x ∈ ⋂ s : U.carrier, s.1 := by
      simp only [Set.iInter_coe_set, Set.mem_iInter]
      intro s hsU
      exact mem_of_isGenericPoint hV hU hx ⟨s, hsU⟩
    exact ne_of_mem_of_not_mem' mem fun h => h
  · simp only [not_nonempty_iff] at h
    rw [← @isCompact_univ_iff X (PatchTopology' X), Set.univ_eq_empty_iff.mpr h]
    simp only [Set.finite_empty, Set.Finite.isCompact]

end PatchTopology'
