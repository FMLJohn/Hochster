import Hochster.Section6

open SpectralSpace SpringLike'.isIndex SWICat

universe u

namespace SpectralSpace

/--
`(firstSWI X).X := X`; `(firstSWI X).E := { s : Set X | IsOpen s ∧ IsCompact s }`;
`(firstSWI X).g := fun e => e.1`.
-/
def firstSWI (X : Type*) [TopologicalSpace X] [SpectralSpace X] :
    SWICat where
  X := X
  tX := inferInstance
  spectralSpace := inferInstance
  E := { s : Set X | IsOpen s ∧ IsCompact s }
  g := fun e => e.1
  forall_isCompact e := e.2.2
  forall_isOpen e := e.2.1
  eq_generateFrom := by
    simpa using SpectralSpace.toPrespectralSpace.isTopologicalBasis.eq_generateFrom

/--
`SpectralSpace.hochsterRing X k` is defined as
`(springLike'_mapRingHomToPiFractionRing_isIndex k (firstSWI X)).iSupExtForV.springLike.spring.A`.
-/
def hochsterRing (X k : Type*) [TopologicalSpace X] [SpectralSpace X] [Field k] :=
  (springLike'_mapRingHomToPiFractionRing_isIndex k (firstSWI X)).iSupExtForV.springLike.spring.A

noncomputable instance (X k : Type*) [TopologicalSpace X] [SpectralSpace X] [Field k] :
    CommRing (hochsterRing X k) := by
  delta hochsterRing
  infer_instance

/--
`SpectralSpace.homeomorph X k` is defined as
`(iSupExtForV_springLike_spring_isAffine_of_isSimple`
  `(((firstSWI X).springLike' k).mapRingHomToPiFractionRingIsSimple`
    `((firstSWI X).closureRangeUnionIsSimple k))`
  `((firstSWI X).springLike'_mapRingHomToPiFractionRing_isIndex k)).homeomorph`.
-/
noncomputable def homeomorph (X k : Type*) [TopologicalSpace X] [SpectralSpace X] [Field k] :
    X ≃ₜ PrimeSpectrum (hochsterRing X k) :=
  (iSupExtForV_springLike_spring_isAffine_of_isSimple
    (((firstSWI X).springLike' k).mapRingHomToPiFractionRingIsSimple
      ((firstSWI X).closureRangeUnionIsSimple k))
    ((firstSWI X).springLike'_mapRingHomToPiFractionRing_isIndex k)).homeomorph

/--
This is Hochster's Theorem: every spectral space is homeomorphic to the prime spectrum of a
commutative ring.
-/
theorem exists_nonempty_homeomorph (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    ∃ R : Type u, ∃ _ : CommRing R, Nonempty (X ≃ₜ PrimeSpectrum R) :=
  ⟨hochsterRing X ℚ, inferInstance, ⟨homeomorph X ℚ⟩⟩

end SpectralSpace
