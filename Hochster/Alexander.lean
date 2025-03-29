import Mathlib.Topology.Compactness.Compact

open TopologicalSpace

variable {X ι : Type*} [T : TopologicalSpace X] {U : ι → Set X}
variable (hTU : T = generateFrom { U i | i : ι })

theorem alexanderSubbasis :
    (∀ s : Set ι, (⋃ i : s, U i = ⊤ → ∃ t : Finset s, ⋃ i : t, U i = ⊤)) →
    CompactSpace X := by
  intro hι
  rw [← isCompact_univ_iff]
  change IsCompact ⊤
  by_contra hn
  sorry
