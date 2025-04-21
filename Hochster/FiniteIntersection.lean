import Mathlib.Topology.Bases

variable (X : Type*) [TopologicalSpace X]

/--
A collection of closed subsets of `X` has the finite intersection property if every finite
subcollection has nonempty intersection.
-/
structure finiteInterClosedSet where
  S : Set (Set X)
  forall_isClosed : ∀ s : S, IsClosed s.1
  finite_inter : ∀ T : Set (Set X), T ⊆ S → Finite T → ⋂ t : T, t.1 ≠ ∅
