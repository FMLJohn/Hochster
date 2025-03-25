import Mathlib.RingTheory.Spectrum.Prime.Topology

open TopologicalSpace

/--
A topological space is spectral if it is T₀, compact, sober, quasi-separated, and its compact open
subsets form an open basis.
-/
class SpectralSpace (α : Type*) [TopologicalSpace α] : Prop where
  t0_space : T0Space α
  compact_space : CompactSpace α
  quasi_sober : QuasiSober α
  quasi_separated_space : QuasiSeparatedSpace α
  is_basis : Opens.IsBasis { O : Opens α | IsCompact O.carrier }

theorem PrimeSpectrum.spectralSpace (R : Type*) [CommSemiring R] :
    SpectralSpace (PrimeSpectrum R) where
  t0_space := instT0Space
  compact_space := compactSpace
  quasi_sober := quasiSober
  quasi_separated_space := instQuasiSeparatedSpace
  is_basis := by
    have h := @isBasis_basic_opens R _
    rw [Opens.isBasis_iff_nbhd] at h ⊢
    intro U x hx
    obtain ⟨U', h1, h2, h3⟩ := h hx
    use U'
    constructor
    · rw [← h1.choose_spec]
      exact isCompact_basicOpen h1.choose
    · exact ⟨h2, h3⟩
