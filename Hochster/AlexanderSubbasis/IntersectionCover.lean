import Mathlib.Topology.Bases

import Hochster.AlexanderSubbasis.OCWNFS

open TopologicalSpace

variable {X ι : Type*} [T : TopologicalSpace X] [Nonempty X] (h : ¬CompactSpace X)
variable {U : ι → Set X} (hTU : T = generateFrom (U '' ⊤))

namespace TopologicalSpace

/--
The intersection of `U '' ⊤` and `(OpenCoverWithNoFiniteSubcover.Max h).toFun '' ⊤` forms a cover
of `X`.
-/
def IntersectionCover : OpenCover X where
  ι := (U '' ⊤).inter ((OpenCoverWithNoFiniteSubcover.Max h).toFun '' ⊤)
  toFun := fun i => i.1
  covers := by
    by_contra hn
    have h1 : ∃ x : X, x ∉ ⋃ i : (U '' ⊤).inter ((OpenCoverWithNoFiniteSubcover.Max h).toFun '' ⊤),
        i := by
      simpa only [← Set.nonempty_compl, Set.compl_iUnion, Set.nonempty_iInter, Set.mem_iInter,
        Set.mem_iUnion, not_exists, not_and] using hn
    obtain ⟨x, hx⟩ := h1
    have h2 : ∃ i : (OpenCoverWithNoFiniteSubcover.Max h).ι,
        x ∈ (OpenCoverWithNoFiniteSubcover.Max h).toFun i :=
      Set.iUnion_eq_univ_iff.1 (OpenCoverWithNoFiniteSubcover.Max h).covers <| x
    obtain ⟨i, hi⟩ := h2
    have h3 := (IsTopologicalBasis.mem_nhds_iff <| isTopologicalBasis_of_subbasis hTU).1 <|
      IsOpen.mem_nhds ((OpenCoverWithNoFiniteSubcover.Max h).forall_isOpen i) hi
    obtain ⟨O, ⟨S, ⟨hS1, hS2⟩, hS3⟩, hxO, hOi⟩ := h3
    simp only [← hS3] at hxO hOi
    have h4 (s : S) : s.1 ∉ (OpenCoverWithNoFiniteSubcover.Max h).toFun '' ⊤ := by
      simp only [Set.top_eq_univ, Set.image_univ, Set.mem_range, not_exists]
      intro i his
      simp only [Set.top_eq_univ, Set.iUnion_coe_set, Set.image_univ, Set.mem_iUnion, not_exists]
        at hx hS2
      refine hx s ?_ <| hxO s s.2
      · exact Set.mem_inter (hS2 s.2) <| by rw [← his]; exact Set.mem_range_self i
    have h5 (s : S) : IsOpen s.1 := by
      obtain ⟨i, hi1, hi2⟩ := hS2 s.2
      simpa only [← hi2, hTU] using isOpen_generateFrom_of_mem <| Set.mem_image_of_mem U hi1
    refine (OpenCoverWithNoFiniteSubcover.Max h).not_exists ?_
    · use OpenCoverWithNoFiniteSubcover.UnionCover h h5 h4 hOi
      constructor
      · exact OpenCoverWithNoFiniteSubcover.unionCover_ι_finite h hS1 h5 h4 hOi
      · exact OpenCoverWithNoFiniteSubcover.subcover_unionCover_max h h5 h4 hOi
  forall_isOpen := fun i => by
    have := i.2.1
    simp only [Set.top_eq_univ, Set.image_univ] at this
    obtain ⟨j, hj⟩ := this
    simp only [Set.top_eq_univ, ← hj, hTU]
    exact isOpen_generateFrom_of_mem <| Set.mem_image_of_mem U trivial

end TopologicalSpace
