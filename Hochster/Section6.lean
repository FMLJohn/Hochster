import Hochster.Section5

open TopologicalSpace

/-- The category of spaces with indeterminates. -/
@[ext]
structure SWICat where
  X : Type*
  tX : TopologicalSpace X
  spectralSpace : SpectralSpace X
  E : Type*
  g : E → Set X
  forall_isCompact (e : E) : IsCompact (g e)
  forall_isOpen (e : E) : IsOpen (g e)
  eq_generateFrom : tX = generateFrom (Set.range g)

attribute [instance] SWICat.tX SWICat.spectralSpace
