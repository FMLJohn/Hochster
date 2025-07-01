import Mathlib.CategoryTheory.Category.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

import Hochster.Section2

open CategoryTheory PrimeSpectrum RingHom TopologicalSpace Topology

@[ext]
structure SpringCat where
  X : Type*
  tX : TopologicalSpace X
  A : Type*
  commRing : CommRing A
  isReduced : IsReduced A
  f : X → PrimeSpectrum A
  isEmbedding : IsEmbedding f
  range_dense : Dense (Set.range f)
  range_isClosed : IsClosed (X := ConstructibleTop (PrimeSpectrum A)) (Set.range f)

structure SpringLike (X A : Type*) [TopologicalSpace X] [CommRing A] where
  spectralSpace : SpectralSpace X
  i : X → Type*
  forall_commRing (x : X) : CommRing (i x)
  forall_isDomain (x : X) : IsDomain (i x)
  h : A →+* Π x : X, i x
  injective : Function.Injective h
  forall_eq_top (x : X) : { h a x | a : A } = ⊤
  forall_isOpen (a : A) : IsOpen { x : X | h a x ≠ 0 }
  forall_isCompact (a : A) : IsCompact { x : X | h a x ≠ 0 }
  isTopologicalBasis : IsTopologicalBasis { { x : X | h a x ≠ 0 } | a : A }

namespace SpringCat

attribute [instance] SpringCat.tX SpringCat.commRing SpringCat.isReduced

def isAffine (𝔸 : SpringCat) := Set.range 𝔸.f = ⊤

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

instance (𝔸 : SpringCat) : SpectralSpace 𝔸.X :=
  spectralSpace_of_isEmbedding_of_isClosed_constructibleTop_range 𝔸.isEmbedding 𝔸.range_isClosed

lemma isSpectralMap_f (𝔸 : SpringCat) : IsSpectralMap 𝔸.f :=
  ((spectralSpace_and_isSpectralMap_iff_isClosed_constructibleTop_range 𝔸.isEmbedding).2
    𝔸.range_isClosed).2

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

/--
For any spring `𝔸`, we have `SpringLike 𝔸.X 𝔸.A`.
-/
def springLike (𝔸 : SpringCat) : SpringLike 𝔸.X 𝔸.A where
  spectralSpace := inferInstance
  i := fun x => 𝔸.A ⧸ (𝔸.f x).asIdeal
  forall_commRing := inferInstance
  forall_isDomain := inferInstance
  h := 𝔸.inclusionRingHom
  injective := 𝔸.inclusionRingHom_injective
  forall_eq_top := fun _ => by
    ext
    simpa only [Set.top_eq_univ, Set.mem_univ, iff_true] using Quotient.exists_rep _
  forall_isOpen := fun a => by
    simpa only [inclusionRingHom, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ne_eq,
      Ideal.Quotient.eq_zero_iff_mem] using
        𝔸.isEmbedding.eq_induced ▸ (isTopologicalBasis_basic_opens (R := 𝔸.A)).eq_generateFrom ▸
          induced_generateFrom_eq ▸ isOpen_generateFrom_of_mem ⟨basicOpen a, ⟨a, rfl⟩, rfl⟩
  forall_isCompact := fun a => by
    have : { x | a ∉ (𝔸.f x).asIdeal } = 𝔸.f ⁻¹' basicOpen a := rfl
    simpa only [inclusionRingHom, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ne_eq,
      Ideal.Quotient.eq_zero_iff_mem] using
        this ▸ (isSpectralMap_f 𝔸).2 isOpen_basicOpen (isCompact_basicOpen a)
  isTopologicalBasis := by
    have : Set.preimage 𝔸.f '' Set.range (fun a => { x | a ∉ x.asIdeal }) =
        { x | ∃ a, { x | 𝔸.inclusionRingHom a x ≠ 0 } = x } := by
      ext
      simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Set.preimage_setOf_eq,
        inclusionRingHom, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ne_eq,
        Ideal.Quotient.eq_zero_iff_mem, Set.mem_setOf_eq]
    exact this ▸ 𝔸.isEmbedding.eq_induced ▸ isTopologicalBasis_basic_opens.induced 𝔸.f

end SpringCat

instance Pi.isReduced_of_forall_isReduced {α : Type*} (i : α → Type*)
    [∀ a : α, Zero (i a)] [∀ a : α, Pow (i a) ℕ] [∀ a : α, IsReduced (i a)] :
    IsReduced (Π a : α, i a) :=
  (isReduced_iff _).2 fun f ⟨n, hfn⟩ => by
    ext a; exact (isReduced_iff _).1 inferInstance (f a) ⟨n, Pi.pow_apply f n a ▸ hfn ▸ rfl⟩

namespace SpringLike

attribute [instance] SpringLike.forall_commRing SpringLike.forall_isDomain

lemma isReduced {X A : Type*} [TopologicalSpace X] [CommRing A] (hXA : SpringLike X A) :
    IsReduced A :=
  (isReduced_iff A).2 fun a ha => ((RingHom.ker_eq_bot_iff_eq_zero hXA.h).1 <|
    (RingHom.injective_iff_ker_eq_bot hXA.h).1 hXA.injective) a
      (isNilpotent_iff_eq_zero.1 <| IsNilpotent.map ha hXA.h)

/--
Given any topological space `X` and commutative ring `A` with `hXA : SpringLike X A`, if we pick an
arbitrary `x : X`, then there is an ideal of `A` corresponding to `x`, that is,
`{ a : A | hXA.h a x = 0 }`.
-/
def matchingIdeal {X A : Type*} [TopologicalSpace X] [CommRing A] (hXA : SpringLike X A) (x : X) :
    Ideal A where
  carrier := { a : A | hXA.h a x = 0 }
  add_mem' := fun ha hb => Set.mem_setOf_eq ▸ map_add hXA.h .. ▸ Pi.add_apply (hXA.h _) .. ▸
    ha ▸ hb ▸ add_zero (hXA.h _ x)
  zero_mem' := Set.mem_setOf_eq ▸ map_zero hXA.h ▸ rfl
  smul_mem' := fun c a ha => Set.mem_setOf_eq ▸ smul_eq_mul c a ▸ map_mul hXA.h .. ▸
    Pi.mul_apply (hXA.h _) .. ▸ mul_eq_zero_of_right (hXA.h c x) ha

lemma mem_matchingIdeal_iff_eq_zero {X A : Type*} [TopologicalSpace X] [CommRing A]
    (hXA : SpringLike X A) (x : X) (a : A) :
    a ∈ hXA.matchingIdeal x ↔ hXA.h a x = 0 := by
  simp [matchingIdeal]

lemma fun_matchingIdeal_injective {X A : Type*}
    [TopologicalSpace X] [CommRing A] (hXA : SpringLike X A) :
    Function.Injective fun x : X => hXA.matchingIdeal x := by
  intro x y hxy
  simp only [matchingIdeal, Submodule.mk.injEq, AddSubmonoid.mk.injEq,
    AddSubsemigroup.mk.injEq] at hxy
  have (a : A) : x ∈ { x : X | hXA.h a x ≠ 0 } ↔ y ∈ { x : X | hXA.h a x ≠ 0 } :=
    not_iff_not.2 (Set.ext_iff.1 hxy a)
  exact (@IsTopologicalBasis.eq_iff X _ hXA.spectralSpace.toT0Space _ hXA.isTopologicalBasis).2
    fun s ⟨a, has⟩ => has ▸ this a

lemma matchingIdeal_isPrime {X A : Type*} [TopologicalSpace X] [CommRing A]
    (hXA : SpringLike X A) (x : X) :
    (hXA.matchingIdeal x).IsPrime where
  ne_top' := (Ideal.ne_top_iff_one _).2 fun h1x => by simp only [matchingIdeal, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq, map_one, Pi.one_apply,
    one_ne_zero] at h1x
  mem_or_mem' := fun hab => by simpa only [matchingIdeal, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq, map_mul, Pi.mul_apply, mul_eq_zero] using hab

end SpringLike

lemma TopologicalSpace.eq_of_isTopologicalBasis_of_isTopologicalBasis {X : Type*}
    [S : TopologicalSpace X] [T : TopologicalSpace X] {U : Set (Set X)}
    (hSU : IsTopologicalBasis (t := S) U) (hTU : IsTopologicalBasis (t := T) U) :
    S = T :=
  hSU.eq_generateFrom (t := S) ▸ hTU.eq_generateFrom (t := T) ▸ rfl

namespace SpringLike

lemma isEmbedding_fun_matchingIdeal {X A : Type*}
    [TopologicalSpace X] [CommRing A] (hXA : SpringLike X A) :
    IsEmbedding fun x : X =>
      (⟨hXA.matchingIdeal x, hXA.matchingIdeal_isPrime x⟩ : PrimeSpectrum A) where
  eq_induced := by
    have h1 := IsTopologicalBasis.induced (fun x : X =>
      ⟨hXA.matchingIdeal x, hXA.matchingIdeal_isPrime x⟩) (isTopologicalBasis_basic_opens (R := A))
    have h2 : (Set.preimage (fun x =>
        (⟨hXA.matchingIdeal x, matchingIdeal_isPrime hXA x⟩ : PrimeSpectrum A)) ''
          Set.range fun a => { x | a ∉ x.asIdeal }) = { { x | hXA.h a x ≠ 0 } | a : A } := by
      ext
      simp only [matchingIdeal, Set.mem_image, Set.mem_range, exists_exists_eq_and,
        Set.preimage_setOf_eq, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
        Set.mem_setOf_eq]
    exact eq_of_isTopologicalBasis_of_isTopologicalBasis
      (T := induced (fun x => ⟨hXA.matchingIdeal x, matchingIdeal_isPrime hXA x⟩) zariskiTopology)
        hXA.isTopologicalBasis (h2 ▸ h1)
  injective := fun x y hxy =>
    fun_matchingIdeal_injective hXA (PrimeSpectrum.mk.injEq (hXA.matchingIdeal x) _ _ _ ▸ hxy)

lemma isSpectralMap_fun_matchingIdeal {X A : Type*}
    [TopologicalSpace X] [CommRing A] (hXA : SpringLike X A) :
    IsSpectralMap fun x : X =>
      (⟨hXA.matchingIdeal x, hXA.matchingIdeal_isPrime x⟩ : PrimeSpectrum A) where
  isOpen_preimage := hXA.isEmbedding_fun_matchingIdeal.continuous.1
  isCompact_preimage_of_isOpen := by
    intro o ho1 ho2
    obtain ⟨s, hs, hos⟩ := (isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis _
      isTopologicalBasis_basic_opens isCompact_basicOpen o).1 ⟨ho2, ho1⟩
    exact hos ▸ by simpa only [Set.preimage_iUnion] using
      hs.isCompact_biUnion fun a _ => hXA.forall_isCompact a

/--
Given a topological space `X` and a commutative ring `A` with `hXA : SpringLike X A`, we obtain a
spring whose underlying space and ring are `X` and `A` respectively.
-/
def spring {X A : Type*} [TopologicalSpace X] [CommRing A] (hXA : SpringLike X A) :
    SpringCat where
  X := X
  tX := inferInstance
  A := A
  commRing := inferInstance
  isReduced := hXA.isReduced
  f := fun x => ⟨matchingIdeal hXA x, matchingIdeal_isPrime hXA x⟩
  isEmbedding := isEmbedding_fun_matchingIdeal hXA
  range_dense := by
    refine (IsTopologicalBasis.dense_iff isTopologicalBasis_basic_opens).2 fun o ⟨a, ha⟩ ho => ?_
    · have : a ≠ 0 := fun h => by
        have := (h ▸ ha) ▸ ho
        simp only [basicOpen, Submodule.zero_mem, not_true_eq_false, Set.setOf_false,
          Opens.mk_empty, Opens.coe_bot, Set.not_nonempty_empty] at this
      obtain ⟨x, hax⟩ := Function.ne_iff.1 ((map_ne_zero_iff hXA.h hXA.injective).2 this)
      refine ⟨⟨hXA.matchingIdeal x, hXA.matchingIdeal_isPrime x⟩, ha ▸ ?_⟩
      · simpa only [Set.mem_inter_iff, Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff,
          Set.mem_range, exists_apply_eq_apply, and_true] using hax
  range_isClosed := letI := hXA.spectralSpace
    IsSpectralMap.isClosed_range hXA.isSpectralMap_fun_matchingIdeal

end SpringLike

lemma SpringCat.springLike_spring_cancel (𝔸 : SpringCat) :
    𝔸.springLike.spring = 𝔸 := by
  ext
  · rfl
  · rfl
  · rfl
  · rfl
  · refine heq_eq_eq _ _ ▸ ?_
    · ext x a
      simp [springLike, SpringLike.spring, SpringLike.matchingIdeal, inclusionRingHom,
        Ideal.Quotient.eq_zero_iff_mem]
