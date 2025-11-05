import Hochster.Section4

/-- The spring that `hA` represents is simple. -/
structure SpringLike'.isSimple {X : Type*}
    [TopologicalSpace X] {i : X → Type*} [(x : X) → Field (i x)]
    {A : Subring (Π x : X, i x)} (hA : SpringLike' A) where
  F : Type*
  field : Field F
  h (x : X) : A.map (Pi.evalRingHom i x) →+* F
  forall_injective (x : X) : Function.Injective (h x)
  forall_finite (a : A) : { h x ⟨a.1 x, a.1, a.2, rfl⟩ | x : X }.Finite
