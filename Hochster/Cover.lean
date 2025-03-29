import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Topology.Defs.Basic

variable (X : Type*) [TopologicalSpace X]

namespace TopologicalSpace

/--
A cover of a topological space `X` is a collection of subsets of `X` that cover `X`.
-/
structure Cover where
  ι : Type*
  toFun : ι → Set X
  covers : ⋃ i : ι, toFun i = ⊤

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

end TopologicalSpace
