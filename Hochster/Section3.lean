import Mathlib.CategoryTheory.Category.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

import Hochster.Section2

open CategoryTheory ConstructibleTop OreLocalization PrimeSpectrum RingHom TopologicalSpace Topology

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
  -- forall_eq_top (x : X) : { h a x | a : A } = ⊤
  forall_isOpen (a : A) : IsOpen { x : X | h a x ≠ 0 }
  forall_isCompact (a : A) : IsCompact { x : X | h a x ≠ 0 }
  isTopologicalBasis : IsTopologicalBasis { { x : X | h a x ≠ 0 } | a : A }

structure SpringLike' {X : Type*} [TopologicalSpace X] {i : X → Type*}
    [(x : X) → CommRing (i x)] [(x : X) → IsDomain (i x)] (A : Subring (Π x : X, i x)) where
  spectralSpace : SpectralSpace X
  -- forall_eq_top (x : X) : { a x | a ∈ A } = ⊤
  forall_isOpen : ∀ a ∈ A, IsOpen { x : X | a x ≠ 0 }
  forall_isCompact : ∀ a ∈ A, IsCompact { x : X | a x ≠ 0 }
  isTopologicalBasis : IsTopologicalBasis { { x : X | a x ≠ 0 } | a ∈ A }

namespace SpringCat

attribute [instance] SpringCat.tX SpringCat.commRing SpringCat.isReduced

def isAffine (𝔸 : SpringCat) := Set.range 𝔸.f = ⊤

noncomputable def isAffine.homeomorph {𝔸 : SpringCat} (h : 𝔸.isAffine) :
    𝔸.X ≃ₜ PrimeSpectrum 𝔸.A :=
  𝔸.isEmbedding.toHomeomorphOfSurjective (Set.range_eq_univ.mp h)

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
    (Set.image_mono hom1.image_subset).trans hom2.image_subset

instance : Category SpringCat where
  Hom 𝔸 𝔹 := Hom 𝔸 𝔹
  id 𝔸 := Hom.id 𝔸
  comp hom1 hom2 := hom1.comp hom2
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance (𝔸 : SpringCat) : SpectralSpace 𝔸.X :=
  spectralSpace_of_isEmbedding_of_isClosed_constructibleTop_range 𝔸.isEmbedding 𝔸.range_isClosed

lemma isSpectralMap (𝔸 : SpringCat) : IsSpectralMap 𝔸.f :=
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
      obtain ⟨p, hap⟩ : ∃ p : PrimeSpectrum 𝔸.A, a ∉ p.asIdeal := by
        have : a ∉ sInf { I : Ideal 𝔸.A | I.IsPrime } :=
          (nilradical_eq_sInf 𝔸.A ▸ nilradical_eq_zero 𝔸.A) ▸ hna
        simp only [Submodule.mem_sInf, not_forall] at this
        obtain ⟨I, hI, haI⟩ := this
        use ⟨I, hI⟩
      obtain ⟨q, hqa, x, hfxq⟩ := Dense.inter_open_nonempty (𝔸.range_dense)
        (PrimeSpectrum.basicOpen a).carrier (PrimeSpectrum.basicOpen a).is_open'
        (Set.nonempty_of_mem hap)
      have h2 : (Ideal.Quotient.mk (𝔸.f x).asIdeal) a ≠ 0 :=
        hfxq ▸ fun hqa0 => hqa <| Ideal.Quotient.eq_zero_iff_mem.1 hqa0
      exact h2 <| h1 x

def springLike (𝔸 : SpringCat) : SpringLike 𝔸.X 𝔸.A where
  spectralSpace := inferInstance
  i := fun x => 𝔸.A ⧸ (𝔸.f x).asIdeal
  forall_commRing := inferInstance
  forall_isDomain := inferInstance
  h := 𝔸.inclusionRingHom
  injective := 𝔸.inclusionRingHom_injective
  -- forall_eq_top := fun _ => by
  --   ext
  --   simpa only [Set.top_eq_univ, Set.mem_univ, iff_true] using Quotient.exists_rep _
  forall_isOpen := fun a => by
    simpa only [inclusionRingHom, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ne_eq,
      Ideal.Quotient.eq_zero_iff_mem] using
        𝔸.isEmbedding.eq_induced ▸ (isTopologicalBasis_basic_opens (R := 𝔸.A)).eq_generateFrom ▸
          induced_generateFrom_eq ▸ isOpen_generateFrom_of_mem ⟨basicOpen a, ⟨a, rfl⟩, rfl⟩
  forall_isCompact := fun a => by
    have : { x | a ∉ (𝔸.f x).asIdeal } = 𝔸.f ⁻¹' basicOpen a := rfl
    simpa only [inclusionRingHom, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ne_eq,
      Ideal.Quotient.eq_zero_iff_mem] using
        this ▸ (isSpectralMap 𝔸).2 isOpen_basicOpen (isCompact_basicOpen a)
  isTopologicalBasis := by
    have : Set.preimage 𝔸.f '' Set.range (fun a => { x | a ∉ x.asIdeal }) =
        { x | ∃ a, { x | 𝔸.inclusionRingHom a x ≠ 0 } = x } := by
      ext
      simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Set.preimage_setOf_eq,
        inclusionRingHom, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ne_eq,
        Ideal.Quotient.eq_zero_iff_mem, Set.mem_setOf_eq]
    exact this ▸ 𝔸.isEmbedding.eq_induced ▸ isTopologicalBasis_basic_opens.induced 𝔸.f

lemma springLike' (𝔸 : SpringCat) : SpringLike' 𝔸.inclusionRingHom.range where
  spectralSpace := inferInstance
  -- forall_eq_top := fun _ => by
  --   ext
  --   simpa only [mem_range, exists_exists_eq_and, Set.top_eq_univ, Set.mem_univ, iff_true]
  --     using Quotient.exists_rep _
  forall_isOpen := fun a ⟨b, hba⟩ => hba ▸ 𝔸.springLike.forall_isOpen b
  forall_isCompact := fun a ⟨b, hba⟩ => hba ▸ 𝔸.springLike.forall_isCompact b
  isTopologicalBasis := by
    simpa only [mem_range, exists_exists_eq_and] using 𝔸.springLike.isTopologicalBasis

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
def matchingIdeal {X A : Type*} [TopologicalSpace X] [CommRing A]
    (hXA : SpringLike X A) (x : X) : Ideal A :=
  RingHom.ker ((Pi.evalRingHom hXA.i x).comp hXA.h)

lemma mem_matchingIdeal_iff_eq_zero {X A : Type*} [TopologicalSpace X] [CommRing A]
    (hXA : SpringLike X A) (x : X) (a : A) :
    a ∈ hXA.matchingIdeal x ↔ hXA.h a x = 0 := by
  rfl

lemma fun_matchingIdeal_injective {X A : Type*}
    [TopologicalSpace X] [CommRing A] (hXA : SpringLike X A) :
    Function.Injective fun x : X => hXA.matchingIdeal x := by
  intro x y hxy
  simp only [Ideal.ext_iff] at hxy
  have (a : A) : x ∈ { x : X | hXA.h a x ≠ 0 } ↔ y ∈ { x : X | hXA.h a x ≠ 0 } :=
    not_iff_not.2 (hxy a)
  exact (@IsTopologicalBasis.eq_iff X _ hXA.spectralSpace.toT0Space _ hXA.isTopologicalBasis).2
    fun s ⟨a, has⟩ => has ▸ this a

lemma matchingIdeal_isPrime {X A : Type*} [TopologicalSpace X] [CommRing A]
    (hXA : SpringLike X A) (x : X) : (hXA.matchingIdeal x).IsPrime := ker_isPrime _

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
        Set.preimage_setOf_eq, mem_ker, coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
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

noncomputable def spring.isAffine.homeomorph {X A : Type*}
    [TopologicalSpace X] [CommRing A] {hXA : SpringLike X A} (h : hXA.spring.isAffine) :
    X ≃ₜ PrimeSpectrum A := h.homeomorph

lemma springLike' {X A : Type*} [TopologicalSpace X] [CommRing A] (hXA : SpringLike X A) :
    SpringLike' hXA.h.range where
  spectralSpace := hXA.spectralSpace
  -- forall_eq_top := fun x => by
  --   simpa only [mem_range, exists_exists_eq_and] using hXA.forall_eq_top x
  forall_isOpen := fun a ⟨b, hba⟩ => hba ▸ hXA.forall_isOpen b
  forall_isCompact := fun a ⟨b, hba⟩ => hba ▸ hXA.forall_isCompact b
  isTopologicalBasis := by simpa only [mem_range, exists_exists_eq_and] using hXA.isTopologicalBasis

end SpringLike

namespace SpringLike'

def springLike {X : Type*} [TopologicalSpace X] {i : X → Type*}
    [(x : X) → CommRing (i x)] [(x : X) → IsDomain (i x)]
    {A : Subring (Π x : X, i x)} (hA : SpringLike' A) :
    SpringLike X A where
  spectralSpace := hA.spectralSpace
  i := i
  forall_commRing := inferInstance
  forall_isDomain := inferInstance
  h := A.subtype
  injective := A.subtype_injective
  -- forall_eq_top := fun x => by
  --   simpa only [Subring.subtype_apply, Subtype.exists, exists_prop] using hXA.forall_eq_top x
  forall_isOpen := fun a => by
    simpa only [SetLike.coe_mem, forall_const] using hA.forall_isOpen a
  forall_isCompact := fun a => by
    simpa only [SetLike.coe_mem, forall_const] using hA.forall_isCompact a
  isTopologicalBasis := by
    simpa only [Subring.subtype_apply, Subtype.exists, exists_prop] using hA.isTopologicalBasis

lemma isReduced {X : Type*} [TopologicalSpace X] {i : X → Type*}
    [(x : X) → CommRing (i x)] [(x : X) → IsDomain (i x)]
    {A : Subring (Π x : X, i x)} (hA : SpringLike' A) :
    IsReduced A := hA.springLike.isReduced

noncomputable def springLike.spring.isAffine.homeomorph {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → CommRing (i x)] [(x : X) → IsDomain (i x)]
    {A : Subring (Π x : X, i x)} {hA : SpringLike' A} (h : hA.springLike.spring.isAffine) :
    X ≃ₜ PrimeSpectrum A := h.homeomorph

end SpringLike'

lemma SpringCat.springLike_spring_f (𝔸 : SpringCat) :
    𝔸.springLike.spring.f = 𝔸.f := by
  ext
  simp [springLike, SpringLike.spring, SpringLike.matchingIdeal, inclusionRingHom,
    Ideal.Quotient.eq_zero_iff_mem]

lemma SpringCat.springLike_matchingIdeal {𝔸 : SpringCat} (x : 𝔸.X) :
    𝔸.springLike.matchingIdeal x = (𝔸.f x).asIdeal :=
  springLike_spring_f 𝔸 ▸ rfl

lemma SpringCat.springLike_spring_cancel (𝔸 : SpringCat) :
    𝔸.springLike.spring = 𝔸 :=
  SpringCat.ext rfl (by rfl) rfl (by rfl) (heq_eq_eq .. ▸ springLike_spring_f _)

lemma PrimeSpectrum.zeroLocus_singleton {R : Type*} [CommSemiring R] (r : R) :
    zeroLocus {r} = { p | r ∈ p.asIdeal } := by
  simp [zeroLocus]

lemma PrimeSpectrum.ConstructibleTop.isTopologicalBasis_inter_biInter (A : Type*) [CommSemiring A] :
    IsTopologicalBasis (α := ConstructibleTop (PrimeSpectrum A))
      { s | ∃ a : A, ∃ B : Set A, B.Finite ∧
        s = { p | a ∉ p.asIdeal } ∩ ⋂ b ∈ B, { p | b ∈ p.asIdeal } } where
  exists_subset_inter := fun s ⟨a1, B1, hB1, haBs⟩ t ⟨a2, B2, hB2, haBt⟩ x hxst => by
    have ha12 : IsOpen ({ p : PrimeSpectrum A | a1 ∉ p.asIdeal } ∩ { p | a2 ∉ p.asIdeal }) :=
      isOpen_basicOpen.inter isOpen_basicOpen
    have hxa12 : x ∈ { p : PrimeSpectrum A | a1 ∉ p.asIdeal } ∩ { p | a2 ∉ p.asIdeal } :=
      Set.mem_inter (Set.mem_of_mem_inter_left <| Set.inter_assoc .. ▸ haBs ▸ hxst)
        (Set.mem_of_mem_inter_left <| Set.inter_assoc .. ▸ Set.inter_comm .. ▸ haBt ▸ hxst)
    obtain ⟨o, ⟨r, hr⟩, hxo, hoa12⟩ := isTopologicalBasis_basic_opens.isOpen_iff.1 ha12 x hxa12
    refine ⟨o ∩ ⋂ b ∈ B1 ∪ B2, { p | b ∈ p.asIdeal }, ⟨r, B1 ∪ B2, hB1.union hB2, hr ▸ rfl⟩, ?_, ?_⟩
    · exact Set.mem_inter hxo (Set.biInter_union .. ▸ Set.mem_inter
        (Set.mem_of_mem_inter_right <| Set.inter_assoc .. ▸ Set.inter_comm .. ▸ haBs ▸ hxst)
        (Set.mem_of_mem_inter_right <| Set.inter_assoc .. ▸ haBt ▸ hxst))
    · exact haBs ▸ haBt ▸ Set.biInter_union .. ▸ Set.inter_inter_inter_comm .. ▸
        Set.inter_subset_inter_left _ hoa12
  sUnion_eq := by
    ext x
    simp only [Set.mem_univ, iff_true]
    exact ⟨(basicOpen 1).1, ⟨1, ∅, Set.finite_empty, Set.biInter_empty _ ▸ Set.inter_univ _ ▸ rfl⟩,
      basicOpen_one (R := A) ▸ Set.mem_univ x⟩
  eq_generateFrom := by
    have : generateFrom { s : Set (PrimeSpectrum A) | ∃ a : A, ∃ B : Set A, B.Finite ∧
        s = { p | a ∉ p.asIdeal } ∩ ⋂ b ∈ B, { p | b ∈ p.asIdeal } } ≤ zariskiTopology :=
      (isTopologicalBasis_basic_opens (R := A)).eq_generateFrom ▸
        le_generateFrom fun s ⟨a, has⟩ => has ▸ isOpen_generateFrom_of_mem
          ⟨a, ⟨∅, Set.finite_empty, Set.biInter_empty _ ▸ Set.inter_univ _ ▸ rfl⟩⟩
    refine instTopologicalSpace_eq_generateFrom_isOpen_isCompact_union_compl_image (PrimeSpectrum A)
      ▸ eq_of_le_of_ge ?_ ?_
    · exact le_generateFrom fun s ⟨a, B, hB, hsaB⟩ =>
        hsaB ▸ @IsOpen.inter _ (generateFrom _) _ _
          (isOpen_generateFrom_of_mem <| Or.intro_left _ ⟨isOpen_basicOpen, isCompact_basicOpen a⟩)
          (@hB.isOpen_biInter _ _ (generateFrom _) _ _ fun b hbB =>
            isOpen_generateFrom_of_mem <| Or.intro_right _
              ⟨basicOpen b, ⟨isOpen_basicOpen, isCompact_basicOpen b⟩, compl_eq_comm.mp rfl⟩)
    · refine le_generateFrom fun s hs => Or.elim hs (fun ⟨hs1, hs2⟩ => this s hs1) ?_
      · intro ⟨t, ⟨ht1, ht2⟩, hts⟩
        obtain ⟨B, hB, htB⟩ := eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _
          isTopologicalBasis_basic_opens t ht2 ht1
        refine hts ▸ htB ▸ isOpen_generateFrom_of_mem ⟨1, B, hB, ?_⟩
        · change _ = (basicOpen 1).1 ∩ _
          refine basicOpen_one (R := A) ▸ Set.univ_inter _ ▸ ?_
          · simp only [basicOpen_eq_zeroLocus_compl, Set.compl_iUnion, compl_compl]
            exact Set.iInter_congr fun a => Set.iInter_congr fun _ => zeroLocus_singleton a

lemma TopologicalSpace.IsTopologicalBasis.exists_mem_compl_of_isClosed_of_ne_univ
    {X : Type*} [TopologicalSpace X] {B : Set (Set X)} (hB : IsTopologicalBasis B)
    {s : Set X} (hs1 : IsClosed s) (hs2 : s ≠ Set.univ) :
    ∃ t ∈ compl '' B, s ⊆ t ∧ t ≠ Set.univ := by
  obtain ⟨S, hSB, hsS⟩ := hB.open_eq_sUnion hs1.isOpen_compl
  have : ∃ t ∈ S, t ≠ ∅ := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hs2 <| Set.compl_empty_iff.mp <| Set.sUnion_eq_empty.2 h ▸ hsS
  obtain ⟨t, htS, ht⟩ := this
  exact ⟨tᶜ, ⟨t, hSB htS, rfl⟩, Set.subset_compl_comm.2 <| hsS ▸ Set.subset_sUnion_of_mem htS,
    fun h => ht <| Set.compl_univ_iff.mp h⟩

/--
The `SpringLike` version of Theorem 2 in Hochster's paper.
-/
lemma SpringLike.spring_isAffine_iff_forall_mem_radical_of_subset
    {X A : Type*} [TopologicalSpace X] [CommRing A] (hXA : SpringLike X A) :
    hXA.spring.isAffine ↔
      ∀ a : A, ∀ B : Set A, B.Finite →
        ⋂ b ∈ B, { x : X | hXA.h b x = 0 } ⊆ { x : X | hXA.h a x = 0 } →
          a ∈ (Ideal.span B).radical := by
  refine ⟨fun h a B hB hBa => ?_, ?_⟩
  · exact Ideal.radical_eq_sInf (Ideal.span B) ▸ Ideal.mem_sInf.2 fun {I} ⟨hIB, hI⟩ => by
      obtain ⟨x, hxI⟩ := le_of_eq h.symm (Set.mem_univ ⟨I, hI⟩)
      simp only [spring, PrimeSpectrum.mk.injEq] at hxI
      exact hxI ▸ (mem_matchingIdeal_iff_eq_zero ..).2 <| hBa <| Set.mem_biInter fun b hbB =>
        (mem_matchingIdeal_iff_eq_zero ..).1 <| hxI ▸ hIB <| Ideal.subset_span hbB
  · intro h
    by_contra neq
    · obtain ⟨s, ⟨t, ⟨a, B, hB, htaB⟩, hts⟩, hs1, hs2⟩ :=
        IsTopologicalBasis.exists_mem_compl_of_isClosed_of_ne_univ
        (ConstructibleTop.isTopologicalBasis_inter_biInter A) hXA.spring.range_isClosed neq
      simp only [htaB, Set.compl_inter, Set.compl_iInter] at hts
      have : ⋂ b ∈ B, { x : X | hXA.h b x = 0 } ⊆ { x : X | hXA.h a x = 0 } := by
        intro x hxB
        have := hts ▸ hs1 (Set.mem_range_self x)
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, not_not,
          Set.mem_iUnion] at this
        exact or_iff_not_imp_right.1 this <| by
          simpa only [not_exists, not_not, Set.mem_iInter] using hxB
      refine hs2 (hts ▸ ?_)
      · ext x
        have := h a B hB this
        simp only [Ideal.radical_eq_sInf, Ideal.mem_sInf, Set.mem_setOf_eq, and_imp] at this
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, not_not, Set.mem_iUnion,
          exists_prop, Set.mem_univ, iff_true, or_iff_not_imp_right, not_exists, not_and]
        exact fun h => this (Ideal.span_le.mpr h) x.isPrime

/--
The `SpringCat` version of Theorem 2 in Hochster's paper.
-/
lemma SpringCat.isAffine_iff_forall_mem_radical_of_subset (𝔸 : SpringCat) :
    𝔸.isAffine ↔
      ∀ a : 𝔸.A, ∀ B : Set 𝔸.A, B.Finite →
        ⋂ b ∈ B, { x : 𝔸.X | b ∈ (𝔸.f x).asIdeal } ⊆ { x : 𝔸.X | a ∈ (𝔸.f x).asIdeal } →
          a ∈ (Ideal.span B).radical := by
  simpa only [springLike_spring_cancel, ← SpringLike.mem_matchingIdeal_iff_eq_zero,
    springLike_matchingIdeal] using 𝔸.springLike.spring_isAffine_iff_forall_mem_radical_of_subset

/--
The `SpringLike'` version of Theorem 2 in Hochster's paper.
-/
lemma SpringLike'.springLike_spring_isAffine_iff_forall_mem_radical_of_subset
    {X : Type*} [TopologicalSpace X] {i : X → Type*} [(x : X) → CommRing (i x)]
    [(x : X) → IsDomain (i x)] {A : Subring (Π x : X, i x)} (hA : SpringLike' A) :
    hA.springLike.spring.isAffine ↔
      ∀ a : A, ∀ B : Set A, B.Finite →
        ⋂ b ∈ B, { x : X | b.1 x = 0 } ⊆ { x : X | a.1 x = 0 } →
          a ∈ (Ideal.span B).radical := by
  simpa using hA.springLike.spring_isAffine_iff_forall_mem_radical_of_subset

@[simps!]
def Pi.ringHomToPiFractionRing {α : Type*} (i : α → Type*) [(a : α) → CommRing (i a)] :
    (Π a : α, i a) →+* (Π a : α, FractionRing (i a)) :=
  Pi.ringHom fun a => numeratorRingHom.comp (Pi.evalRingHom i a)

lemma Pi.ringHomToPiFractionRing_injective_of_forall_isDomain
    {α : Type*} (i : α → Type*) [(a : α) → CommRing (i a)] [(a : α) → IsDomain (i a)] :
    Function.Injective (Pi.ringHomToPiFractionRing i) := by
  refine (injective_iff_ker_eq_bot _).2 (Ideal.ext fun h => ?_)
  · change (fun b => h b /ₒ 1) = 0 ↔ _
    refine ⟨fun hh => ?_, fun hh => funext fun a => hh ▸ zero_apply (M := i) a ▸ zero_oreDiv' 1⟩
    · have h1 (a : α) : @oreDiv (i a) _ (nonZeroDivisors (i a)) _ (i a) _ (h a) 1 = 0 := by
        change (fun a => @oreDiv _ _ (nonZeroDivisors (i a)) _ _ _ _ 1) a = 0
        exact hh ▸ rfl
      have h2 (a : α) := @oreDiv_eq_iff (i a) _ (nonZeroDivisors (i a)) _ (i a) _ (h a) 0 1 1
      simp only [zero_oreDiv', smul_zero, smul_eq_mul, zero_eq_mul, OneMemClass.coe_one, mul_one,
        exists_eq_right', nonZeroDivisors.coe_ne_zero, false_or, exists_const] at h2
      exact funext fun a => (h2 a).1 (h1 a)

lemma Pi.ringHomToPiFractionRing_apply_eq_zero_iff_of_forall_isDomain {α : Type*} {i : α → Type*}
    [(a : α) → CommRing (i a)] [(a : α) → IsDomain (i a)] (h : Π a : α, i a) (a : α) :
    h a = 0 ↔ Pi.ringHomToPiFractionRing i h a = 0 := by
  simpa using (@oreDiv_eq_iff _ _ (nonZeroDivisors (i a)) _ (i a) _ _ 0 1 1).symm

lemma Pi.ringHomToPiFractionRing_apply_ne_zero_iff_of_forall_isDomain {α : Type*} {i : α → Type*}
    [(a : α) → CommRing (i a)] [(a : α) → IsDomain (i a)] (h : Π a : α, i a) (a : α) :
    h a ≠ 0 ↔ Pi.ringHomToPiFractionRing i h a ≠ 0 :=
  not_iff_not.2 <| ringHomToPiFractionRing_apply_eq_zero_iff_of_forall_isDomain h a

namespace SpringLike'

lemma mapRingHomToPiFractionRing {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → CommRing (i x)] [(x : X) → IsDomain (i x)]
    {A : Subring (Π x : X, i x)} (hA : SpringLike' A) :
    SpringLike' (A.map (Pi.ringHomToPiFractionRing i)) where
  spectralSpace := hA.spectralSpace
  forall_isOpen := fun h ⟨a, ha, hah⟩ => hah ▸ by
    simpa only [← Pi.ringHomToPiFractionRing_apply_ne_zero_iff_of_forall_isDomain]
      using hA.forall_isOpen a ha
  forall_isCompact := fun h ⟨a, ha, hah⟩ => hah ▸ by
    simpa only [← Pi.ringHomToPiFractionRing_apply_ne_zero_iff_of_forall_isDomain]
      using hA.forall_isCompact a ha
  isTopologicalBasis := by
    refine IsTopologicalBasis.of_isOpen_of_subset (fun s ⟨h, ⟨a, ha, hah⟩, hhs⟩ => hhs ▸ hah ▸ ?_)
      hA.isTopologicalBasis (fun s ⟨a, ha, has⟩ => ?_)
    · simp only [← Pi.ringHomToPiFractionRing_apply_ne_zero_iff_of_forall_isDomain]
      exact hA.forall_isOpen a ha
    · exact ⟨Pi.ringHomToPiFractionRing i a, Subring.mem_map.2 ⟨a, ha, rfl⟩, has ▸ Set.ext
        fun x => (Pi.ringHomToPiFractionRing_apply_ne_zero_iff_of_forall_isDomain a x).symm⟩

lemma closureUnion {X : Type*} [TopologicalSpace X]
    {i : X → Type*} [(x : X) → CommRing (i x)] [(x : X) → IsDomain (i x)]
    {A : Subring (Π x : X, i x)} (hA : SpringLike' A) {B : Set (Π x : X, i x)}
    (hBA : ∀ c ∈ Subring.closure (B ∪ A),
      IsOpen { x : X | c x ≠ 0 } ∧ IsCompact { x : X | c x ≠ 0 }) :
    SpringLike' (Subring.closure (B ∪ A)) where
  spectralSpace := hA.spectralSpace
  forall_isOpen := fun c hc => (hBA c hc).1
  forall_isCompact := fun c hc => (hBA c hc).2
  isTopologicalBasis := IsTopologicalBasis.of_isOpen_of_subset
    (fun _ ⟨c, hc, hcs⟩ => hcs ▸ (hBA c hc).1) hA.isTopologicalBasis
    (fun _ ⟨a, ha, has⟩ => ⟨a, Subring.mem_closure_of_mem (Set.mem_union_right B ha), has⟩)

end SpringLike'
