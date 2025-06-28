import Mathlib.Algebra.Ring.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology

import Hochster.Section2

open CategoryTheory PrimeSpectrum RingHom TopologicalSpace Topology

universe u

structure SpringCat where
  X : Type u
  tX : TopologicalSpace X
  A : Type u
  commRing : CommRing A
  isReduced : IsReduced A
  f : X → PrimeSpectrum A
  isEmbedding : IsEmbedding f
  range_dense : Dense (Set.range f)
  range_isClosed : IsClosed (X := ConstructibleTop (PrimeSpectrum A)) (Set.range f)

namespace SpringCat

attribute [instance] SpringCat.tX SpringCat.commRing SpringCat.isReduced

@[ext]
structure Hom (𝔸 𝔹 : SpringCat) where
  hom' : 𝔹.A →+* 𝔸.A
  image_subset : hom'.specComap '' (Set.range 𝔸.f) ⊆ Set.range 𝔹.f

def Hom.id (𝔸 : SpringCat) : Hom 𝔸 𝔸 where
  hom' := RingHom.id 𝔸.A
  image_subset := by simp

def Hom.comp {𝔸 𝔹 ℂ : SpringCat} (hom1 : 𝔸.Hom 𝔹) (hom2 : 𝔹.Hom ℂ) : 𝔸.Hom ℂ where
  hom' := hom1.hom'.comp hom2.hom'
  image_subset := specComap_comp hom2.hom' hom1.hom' ▸ Set.image_comp _ _ _ ▸
    (Set.image_subset hom2.hom'.specComap hom1.image_subset).trans hom2.image_subset

instance : Category SpringCat where
  Hom 𝔸 𝔹 := Hom 𝔸 𝔹
  id 𝔸 := Hom.id 𝔸
  comp hom1 hom2 := hom1.comp hom2
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

def isAffine (𝔸 : SpringCat) := Set.range 𝔸.f = ⊤

instance (𝔸 : SpringCat) : SpectralSpace 𝔸.X :=
  spectralSpace_of_isEmbedding_of_isClosed_constructibleTop_range 𝔸.isEmbedding 𝔸.range_isClosed

def inclusionRingHom (𝔸 : SpringCat) :
    𝔸.A →+* Π x : 𝔸.X, 𝔸.A ⧸ (𝔸.f x).asIdeal where
  toFun := fun a x => Ideal.Quotient.mk (𝔸.f x).asIdeal a
  map_one' := by ext; simp
  map_mul' := fun _ _ => by ext; simp
  map_zero' := by ext; simp
  map_add' := fun _ _ => by ext; simp

lemma inclusionRingHom_injective (𝔸 : SpringCat) :
    Function.Injective 𝔸.inclusionRingHom := by
  refine (RingHom.injective_iff_ker_eq_bot _).2 ?_
  · ext a
    simp only [inclusionRingHom, mem_ker, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    refine ⟨fun ha => by_contra fun hna => ?_, fun ha => ha ▸ rfl⟩
    · have h1 (x : 𝔸.X) : (Ideal.Quotient.mk (𝔸.f x).asIdeal) a = 0 := by
        change (fun x => (Ideal.Quotient.mk (𝔸.f x).asIdeal) a) x = 0
        exact ha ▸ rfl
      have h2 : ∃ p : PrimeSpectrum 𝔸.A, a ∉ p.asIdeal := by
        have : a ∉ sInf { I : Ideal 𝔸.A | I.IsPrime } :=
          (nilradical_eq_sInf 𝔸.A ▸ nilradical_eq_zero 𝔸.A) ▸ hna
        simp only [Submodule.mem_sInf, not_forall] at this
        obtain ⟨I, hI, haI⟩ := this
        use ⟨I, hI⟩
      obtain ⟨p, hap⟩ := h2
      obtain ⟨q, hqa, x, hfxq⟩ := Dense.inter_open_nonempty (𝔸.range_dense)
        (PrimeSpectrum.basicOpen a).carrier (PrimeSpectrum.basicOpen a).is_open'
        (Set.nonempty_of_mem hap)
      have h3 : (Ideal.Quotient.mk (𝔸.f x).asIdeal) a ≠ 0 :=
        hfxq ▸ fun hqa0 => hqa <| Ideal.Quotient.eq_zero_iff_mem.1 hqa0
      exact h3 <| h1 x

end SpringCat

structure SpringLike (X A : Type*) where
  tX : TopologicalSpace X
  spectralSpace : SpectralSpace X
  commRing : CommRing A
  i : X → Type*
  forall_commRing (x : X) : CommRing (i x)
  forall_isDomain (x : X) : IsDomain (i x)
  h : A →+* Π x : X, i x
  injective : Function.Injective h
  forall_eq_top (x : X) : { h a x | a : A } = ⊤
  forall_isOpen (a : A) : IsOpen { x : X | h a x ≠ 0 }
  forall_isCompact (a : A) : IsCompact { x : X | h a x ≠ 0 }
  isTopologicalBasis : IsTopologicalBasis { { x : X | h a x ≠ 0 } | a : A }
