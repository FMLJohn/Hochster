import Mathlib.Data.Set.Defs
import Mathlib.Topology.Compactness.Compact

import Hochster.OCWNFS

open TopologicalSpace

variable {X ι : Type*} [T : TopologicalSpace X] [Nonempty X] (h : ¬CompactSpace X)
variable {U : ι → Set X} (hTU : T = generateFrom (U '' ⊤))

namespace TopologicalSpace

def IntersectionCover : OpenCover X where
  ι := (U '' ⊤).inter ((OpenCoverWithNoFiniteSubcover.Max h).toFun '' ⊤)
  toFun := fun i => i.1
  covers := by
    by_contra hn
    have h1 : ∃ x : X, x ∉ ⋃ i : (U '' ⊤).inter ((OpenCoverWithNoFiniteSubcover.Max h).toFun '' ⊤),
        (fun i ↦ i) i := by
      simpa only [Set.top_eq_univ, Set.iUnion_coe_set, Set.image_univ, ← Set.nonempty_compl,
        Set.compl_iUnion, Set.nonempty_iInter, Set.mem_iInter, Set.mem_compl_iff, Set.mem_iUnion,
        exists_prop, not_exists, not_and] using hn
    obtain ⟨x, hx⟩ := h1
    have h2 : ∃ i : (OpenCoverWithNoFiniteSubcover.Max h).ι,
        x ∈ (OpenCoverWithNoFiniteSubcover.Max h).toFun i :=
      Set.iUnion_eq_univ_iff.1 (OpenCoverWithNoFiniteSubcover.Max h).covers <| x
    obtain ⟨i, hi⟩ := h2
    have h3 : IsOpen ((OpenCoverWithNoFiniteSubcover.Max h).toFun i) :=
      (OpenCoverWithNoFiniteSubcover.Max h).forall_isOpen i
    let h4 := (TopologicalSpace.IsTopologicalBasis.mem_nhds_iff <|
      TopologicalSpace.isTopologicalBasis_of_subbasis hTU).1 <| IsOpen.mem_nhds h3 hi
    obtain ⟨O, ⟨S, ⟨hS1, hS2⟩, hS3⟩, hS4, hS5⟩ := h4
    simp only [← hS3, Set.mem_sInter] at hS4 hS5
    have h5 (s : S) : s.1 ∉ (OpenCoverWithNoFiniteSubcover.Max h).toFun '' ⊤ := by
      simp only [Set.top_eq_univ, Set.image_univ, Set.mem_range, not_exists]
      intro i his
      simp only [Set.top_eq_univ, Set.iUnion_coe_set, Set.image_univ, Set.mem_iUnion,
        not_exists, not_and] at hx hS2
      refine hx s ?_ <| hS4 s s.2
      · exact Set.mem_inter (hS2 s.2) <| by rw [← his]; exact Set.mem_range_self i
    have h6 (s : S) : IsOpen s.1 := by
      obtain ⟨i, hi1, hi2⟩ := hS2 s.2
      rw [← hi2, hTU]
      exact isOpen_generateFrom_of_mem <| Set.mem_image_of_mem U trivial
    sorry
  forall_isOpen := fun i => by
    have := i.2.1
    simp only [Set.top_eq_univ, Set.image_univ] at this
    obtain ⟨j, hj⟩ := this
    simp only [Set.top_eq_univ, ← hj, hTU]
    exact isOpen_generateFrom_of_mem <| Set.mem_image_of_mem U trivial

end TopologicalSpace
