import Mathlib.Data.Set.Card
import Mathlib.Topology.QuasiSeparated

variable {X : Type*} [TopologicalSpace X] [QuasiSeparatedSpace X]

namespace QuasiSeparatedSpace

lemma oc_sets_closed_under_nonempty_finite_inter' :
    ∀ (n : ℕ) {S : Set (Set X)} (_ : S ⊆ { s : Set X | IsOpen s ∧ IsCompact s })
    (_ : S.Nonempty) (_ : S.Finite) (_ : S.ncard = n), IsCompact (⋂ s ∈ S, s) := by
  intro n
  induction n with
  | zero =>
      intro S hS1 hS2 hS3 hS4
      exfalso
      exact Nat.not_succ_le_zero 0 <| lt_of_lt_of_eq ((Set.ncard_pos hS3).2 hS2) hS4
  | succ n hn =>
      intro S hS1 hS2 hS3 hS4
      obtain ⟨s, hs⟩ := hS2
      by_cases hSs : (S \ {s}).Nonempty
      · have subset : S \ {s} ⊆ { s : Set X | IsOpen s ∧ IsCompact s } :=
          Set.Subset.trans Set.diff_subset hS1
        have finite : (S \ {s}).Finite := Set.Finite.diff hS3
        have ncard_eq : (S \ {s}).ncard = n := by
          apply (Set.ncard_diff (Set.singleton_subset_iff.mpr hs) (Set.finite_singleton s)).trans
          · rw [hS4, Set.ncard_singleton, add_tsub_cancel_right]
        rw [← Set.union_diff_cancel (Set.singleton_subset_iff.mpr hs)]
        simp only [Set.biInter_union, Set.mem_singleton_iff, Set.iInter_iInter_eq_left]
        exact (quasiSeparatedSpace_iff X).1 inferInstance _ _ (hS1 hs).1 (hS1 hs).2
          (Set.Finite.isOpen_biInter finite fun _ h => (hS1 <| Set.mem_of_mem_diff h).1)
          (hn subset hSs finite ncard_eq)
      · have : S = {s} := by
          refine Set.eq_of_subset_of_subset ?_ ?_
          · exact Set.diff_eq_empty.1 <| Set.not_nonempty_iff_eq_empty.1 hSs
          · exact Set.singleton_subset_iff.mpr hs
        simp only [this, Set.mem_singleton_iff, Set.iInter_iInter_eq_left]
        exact (hS1 hs).2

lemma oc_sets_closed_under_nonempty_finite_inter {S : Set (Set X)}
    (hS1 : S ⊆ { s : Set X | IsOpen s ∧ IsCompact s }) (hS2 : S.Nonempty) (hS3 : S.Finite) :
    IsCompact (⋂ s ∈ S, s) :=
  oc_sets_closed_under_nonempty_finite_inter' S.ncard hS1 hS2 hS3 rfl

end QuasiSeparatedSpace
