import Mathlib.Algebra.Ring.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology

import Hochster.Section2

open CategoryTheory PrimeSpectrum RingHom Topology

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

instance (𝔸 : SpringCat) : TopologicalSpace 𝔸.X := 𝔸.tX

instance (𝔸 : SpringCat) : CommRing 𝔸.A := 𝔸.commRing

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

end SpringCat

def IsAffine (𝔸 : SpringCat) := Set.range 𝔸.f = ⊤
