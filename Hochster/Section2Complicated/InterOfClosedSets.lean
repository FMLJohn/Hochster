import Mathlib.Topology.Sober

import Hochster.Section2Complicated.FiniteIntersection
import Hochster.Section2Complicated.QuasiSeparated

open FiniteInterClosedSubbasisSet QuasiSeparatedSpace TopologicalSpace

universe u
variable {X ι : Type u} [R : TopologicalSpace X] [T : TopologicalSpace X]
variable (hT : T = generateFrom { S : Set X | @IsOpen X T S ∧ @IsCompact X T S })
variable {V : ι → Set X} (hRV : R = generateFrom { (V i)ᶜ | i : ι })
variable (hV : { V i | i : ι } = { S : Set X | @IsClosed X T S } ∪
  { S : Set X | @IsOpen X T S ∧ @IsCompact X T S })
variable (U : FiniteInterClosedSubbasisSet V) (hU : IsMax U)

open Classical

omit R in
include hU hV in
variable {U} in
lemma sInter_of_oc_sets_mem [QuasiSeparatedSpace X] {S : Set (Set X)} (hS1 : S ⊆ U.carrier)
    (hS2 : S ⊆ { s : Set X | IsOpen s ∧ IsCompact s }) (hS3 : Nonempty S) (hS4 : Finite S) :
    ⋂ s ∈ S, s ∈ U.carrier := by
  let ficss : FiniteInterClosedSubbasisSet V := {
    carrier := Set.insert (⋂ s ∈ S, s) U.carrier
    forall_mem := by
      intro s
      refine Or.elim (Set.mem_insert_iff.1 s.2) ?_ ?_
      · intro hs
        rw [hV]
        refine Set.mem_union_right _ ?_
        · constructor
          · simpa only [hs] using Set.Finite.isOpen_biInter hS4 fun _ h => (hS2 h).1
          · simpa only [hs] using oc_sets_closed_under_nonempty_finite_inter hS2
              Set.Nonempty.of_subtype hS4
      · exact fun hs => U.forall_mem ⟨s, hs⟩
    finite_inter := by
      intro S' subset nonempty finite
      by_cases hSs' : ⋂ s ∈ S, s ∈ S'
      · have eq : ⋂ s : S', s.1 = ⋂ s : ((S' ∩ U.carrier) ∪ S : Set (Set X)), s.1 := by
          have : ⋂ s : ((S' ∩ U.carrier) ∪ S : Set (Set X)), s.1 =
              (⋂ s : (S' ∩ U.carrier : Set (Set X)), s.1) ∩ (⋂ s : S, s.1) := by
            ext x
            simp only [Set.iInter_coe_set, Set.mem_inter_iff, Set.mem_iInter, and_imp]
            constructor
            · intro forall_imp
              constructor
              · intro s hs1 hs2
                exact forall_imp s <| Or.intro_left _ ⟨hs1, hs2⟩
              · intro s hs
                exact forall_imp s <| Or.intro_right _ hs
            · rintro ⟨h1, h2⟩ s hs
              exact Or.elim hs (fun h => h1 s h.1 h.2) (fun h => h2 s h)
          rw [this]
          ext x
          constructor
          · intro hx
            constructor
            · simp only [Set.iInter_coe_set, Set.mem_iInter, Set.mem_inter_iff, and_imp] at hx ⊢
              intro s hs1 hs2
              exact hx s hs1
            · simp only [Set.iInter_coe_set, Set.mem_iInter] at hx
              simpa only [Set.iInter_coe_set] using hx (⋂ s ∈ S, s) hSs'
          · intro h
            simp only [Set.iInter_coe_set, Set.mem_iInter]
            intro s hs
            by_cases hsU : s ∈ U.carrier
            · have := h.1
              simp only [Set.iInter_coe_set, Set.mem_inter_iff, Set.mem_iInter, and_imp] at this
              exact this s hs hsU
            · rw [Decidable.or_iff_not_imp_right.1 (Set.mem_insert_iff.1 <| subset hs) hsU]
              simpa only [Set.iInter_coe_set] using h.2
        rw [eq]
        have subset' : (S' ∩ U.carrier ∪ S : Set (Set X)) ⊆ U.carrier :=
          Set.union_subset Set.inter_subset_right hS1
        have nonempty' : Nonempty (S' ∩ U.carrier ∪ S : Set (Set X)) :=
          Set.Nonempty.to_subtype <| Set.union_nonempty.2 <| Or.intro_right _ <|
            Set.Nonempty.of_subtype
        have finite' : Finite (S' ∩ U.carrier ∪ S : Set (Set X)) :=
          Set.Finite.union (Set.Finite.inter_of_left finite U.carrier) hS4
        exact U.finite_inter _ subset' nonempty' finite'
      · exact U.finite_inter S' ((Set.subset_insert_iff_of_not_mem hSs').1 subset) nonempty finite }
  by_contra hSU
  have lt : U < ficss := by
    refine lt_of_le_of_ne ?_ ?_
    · intro s hs
      exact Set.mem_insert_iff.2 <| Or.inr hs
    · intro eq
      rw [eq] at hSU
      exact hSU <| Set.mem_insert (⋂ s ∈ S, s) U.carrier
  exact (not_le_of_lt <| lt) (hU <| le_of_lt lt)

/--
The intersection of all elements in `U.carrier` which are closed in terms of `T`.
-/
def InterOfClosedSets : Set X :=
  ⋂₀ (U.carrier ∩ { S : Set X | @IsClosed X T S })

namespace InterOfClosedSets

omit R in
lemma isClosed : @IsClosed X T (@InterOfClosedSets X ι T V U) := by
  refine @isClosed_sInter X T _ ?_
  · simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_imp, imp_self, implies_true]

omit R in
lemma nonempty [Nonempty X] [@CompactSpace X T] :
    (@InterOfClosedSets X ι T V U).Nonempty := by
  let ι' := { S : Set X | @IsClosed X T S }
  let V' : ι' → Set X := fun i => i.1
  have hTV' : T = generateFrom { (V' i)ᶜ | i : ι' } := by
    have : { S : Set X | ∃ C : Set X, IsClosed C ∧ Cᶜ = S } = { S : Set X | IsOpen S } := by
      ext S
      constructor
      · rintro ⟨C, hC1, hC2⟩
        rw [← hC2]
        exact IsClosed.isOpen_compl
      · intro hS
        exact ⟨Sᶜ, isClosed_compl_iff.mpr hS, compl_compl S⟩
    simp only [V', ι', Set.coe_setOf, Subtype.exists, exists_prop, this]
    exact (generateFrom_setOf_isOpen T).symm
  let ficss : FiniteInterClosedSubbasisSet V' := {
    carrier := U.carrier ∩ { S : Set X | @IsClosed X T S }
    forall_mem := by
      simp only [Subtype.exists, Subtype.forall, Set.mem_inter_iff, and_imp]
      intro S hS1 hS2
      use S
      use hS2
    finite_inter := by
      intro S hS1 hS2 hS3
      exact U.finite_inter S (Set.subset_inter_iff.1 hS1).1 hS2 hS3 }
  simpa only [InterOfClosedSets, Set.sInter_eq_iInter] using
    Set.nonempty_iff_ne_empty.mpr <| forall_of_CompactSpace hTV' inferInstance ficss

variable {U}

omit R in
include hV in
lemma forall_inter_nonempty [Nonempty X] [@CompactSpace X T] (S : U.carrier) :
    (S.1 ∩ (@InterOfClosedSets X ι T V U)).Nonempty := by
  have mem := U.forall_mem S
  rw [hV] at mem
  unfold InterOfClosedSets
  refine Or.elim mem ?_ ?_
  · intro hS
    have : ⋂₀ (U.carrier ∩ { S : Set X | @IsClosed X T S }) ⊆ S.1 :=
      fun _ mem => mem S.1 <| Set.mem_inter S.2 hS
    rw [Set.inter_eq_right.2 this]
    exact nonempty U
  · rintro ⟨hS1, hS2⟩
    let ι' := U.carrier ∩ { S : Set X | @IsClosed X T S }
    let V' : ι' → Set X := fun i => i.1
    have imp := Decidable.not_imp_not.2 <| (@isCompact_iff_finite_subfamily_closed X T S.1).1 hS2 V'
      (fun i => i.2.2)
    simp only [not_exists] at imp
    have forall_nonempty : ∀ s : Finset ι', ¬S.1 ∩ ⋂ i ∈ s, V' i = ∅ := by
      intro s h
      have subset : ({ S.1 } ∪ { i.1 | i : s } : Set (Set X)) ⊆ U.carrier := by
        simp only [Subtype.exists, exists_prop, exists_and_right, exists_eq_right]
        intro t ht
        refine Or.elim ht ?_ ?_
        · intro htS
          rw [htS]
          exact S.2
        · rintro ⟨h1, h2⟩
          exact Set.mem_of_mem_inter_left h1
      have nonempty : ({ S.1 } ∪ { i.1 | i : s } : Set (Set X)).Nonempty :=
        Set.union_nonempty.2 <| Or.intro_left _ <| Set.singleton_nonempty _
      have finite : ({ S.1 } ∪ { i.1 | i : s } : Set (Set X)).Finite := by
        refine Set.finite_union.2 ⟨?_, ?_⟩
        · exact Set.finite_singleton _
        · have : { i.1.1 | i : s } = s.toSet := by
            ext
            simp only [Subtype.exists, exists_prop, Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
          rw [this]
          exact Set.Finite.image Subtype.val <| Finite.of_fintype _
      have eq : S.1 ∩ ⋂ i ∈ s, V' i = ⋂ t : ({ S.1 } ∪ { i.1 | i : s } : Set (Set X)), t.1 := by
        simp only [Set.iInter_coe_set, Set.singleton_union, Subtype.exists, exists_prop,
          exists_and_right, exists_eq_right, Set.mem_insert_iff, Set.mem_setOf_eq,
          Set.iInter_iInter_eq_or_left, Set.iInter_exists]
        rfl
      exact U.finite_inter _ subset nonempty.to_subtype finite <| eq.symm.trans h
    have eq : S.1 ∩ ⋂₀ (U.carrier ∩ { S : Set X | IsClosed S }) = S.1 ∩ (⋂ i : ι', V' i) := by
      ext
      simp only [Set.mem_inter_iff, Set.mem_sInter, Set.iInter_coe_set, Set.mem_iInter, ι', V']
    rw [eq]
    exact Set.nonempty_iff_ne_empty.mpr (imp forall_nonempty)

/--
`(FICSSOfInsert hV hU).carrier = U.carrier ∪ { InterOfClosedSets U }`.
-/
def FICSSOfInsert [Nonempty X] [CompactSpace X] [QuasiSeparatedSpace X] :
    FiniteInterClosedSubbasisSet V where
  carrier := U.carrier ∪ { InterOfClosedSets U }
  forall_mem := by
    intro s
    have mem := s.2
    simp only [Set.union_singleton] at mem
    refine Or.elim mem ?_ ?_
    · intro hs
      simp only [hV]
      refine Or.intro_left _ ?_
      · rw [hs]
        exact isClosed U
    · intro hs
      exact U.forall_mem ⟨s, hs⟩
  finite_inter := by
    intro T' subset nonempty finite
    by_cases hT' : InterOfClosedSets U ∈ T'
    · have h1 : T' = (T' ∩ U.carrier) ∪ { InterOfClosedSets U } := by
        ext
        simp only [Set.union_singleton]
        constructor
        · intro hsT'
          exact Or.elim (subset hsT') (fun h => Or.intro_right _ ⟨hsT', h⟩) (fun h => Or.inl h)
        · intro hsTU'
          exact Or.elim hsTU' (fun h => Set.mem_of_eq_of_mem h hT')
            (fun h => Set.mem_of_mem_inter_right h.symm)
      have h2 : T' ∩ U.carrier = ((T' ∩ U.carrier) ∩ { s | IsClosed s }) ∪
          ((T' ∩ U.carrier) ∩ { s | IsOpen s ∧ IsCompact s }) := by
        rw [← Set.inter_union_distrib_left, ← hV, Set.inter_assoc,
          Set.inter_eq_left.2 (fun s hs => U.forall_mem ⟨s, hs⟩)]
      have h3 : InterOfClosedSets U ⊆ ⋂ s ∈ T' ∩ U.carrier ∩ { s | IsClosed s }, s := by
        intro x
        simp only [InterOfClosedSets, Set.mem_sInter, Set.mem_inter_iff, and_imp, Set.mem_iInter]
        intro forall_imp s hsT' hsU closed
        exact forall_imp s hsU closed
      rw [h1]
      simp only [Set.iInter_coe_set, Set.union_singleton, Set.mem_insert_iff,
        Set.iInter_iInter_eq_or_left]
      rw [h2, Set.biInter_union, ← Set.inter_assoc, Set.inter_eq_left.2 h3]
      by_cases empty : (T' ∩ U.carrier ∩ { S | IsOpen S ∧ IsCompact S } : Set (Set X)) = ∅
      · simpa only [empty, Set.mem_empty_iff_false, Set.iInter_of_empty, Set.iInter_univ,
          Set.inter_univ] using Set.nonempty_iff_ne_empty.mp <| InterOfClosedSets.nonempty U
      · have : ⋂ s ∈ T' ∩ U.carrier ∩ { s | IsOpen s ∧ IsCompact s }, s ∈ U.carrier := by
          refine sInter_of_oc_sets_mem hV hU ?_ Set.inter_subset_right ?_ ?_
          · rw [Set.inter_comm, ← Set.inter_assoc]
            exact Set.inter_subset_right
          · exact Set.nonempty_iff_ne_empty'.mpr empty
          · rw [Set.inter_assoc]
            exact Finite.Set.finite_inter_of_left T' _
        rw [Set.inter_comm]
        exact Set.nonempty_iff_ne_empty'.mp <| Set.Nonempty.coe_sort <| forall_inter_nonempty hV
          ⟨_, this⟩
    · have : T' ⊆ U.carrier := by
        simp only [Set.union_singleton] at subset
        exact (Set.subset_insert_iff_of_not_mem hT').mp subset
      exact U.finite_inter T' this nonempty finite

omit R in
include hU hV in
lemma mem_carrier [Nonempty X] [CompactSpace X] [QuasiSeparatedSpace X] :
    InterOfClosedSets U ∈ U.carrier := by
  by_contra h
  have : U < FICSSOfInsert hV hU := by
    refine lt_of_le_of_ne ?_ ?_
    · intro s hsU
      exact Set.mem_union_left _ hsU
    · intro eq
      have : InterOfClosedSets U ∈ (FICSSOfInsert hV hU).carrier :=
        Set.mem_union_right U.carrier rfl
      rw [← eq] at this
      exact h this
  exact (not_le_of_lt <| this) (hU <| le_of_lt this)

omit R in
include hU hV in
lemma forall_inter_or_forall_inter_of_union_eq [Nonempty X] [CompactSpace X]
    [QuasiSeparatedSpace X] {s₁ s₂ : Set X} (h : s₁ ∪ s₂ = InterOfClosedSets U) :
    (∀ s : U.carrier, s.1 ∩ s₁ ≠ ∅) ∨ (∀ s : U.carrier, s.1 ∩ s₂ ≠ ∅) := by
  refine Decidable.or_iff_not_imp_left.2 ?_
  · simp only [Subtype.forall, not_forall, Decidable.not_not, forall_exists_index]
    intro s hsU hss₁ t htU hts₂
    have subset : { s, t, InterOfClosedSets U } ⊆ U.carrier := by
      intro r hr
      refine Or.elim hr ?_ ?_
      · intro hrs
        rw [hrs]
        exact hsU
      · intro hrtI
        refine Or.elim hrtI ?_ ?_
        · intro hrt
          rw [hrt]
          exact htU
        · intro hrI
          rw [hrI]
          exact mem_carrier hV hU
    refine U.finite_inter { s, t, InterOfClosedSets U } subset (Set.instNonemptyElemInsert s _)
      (Finite.Set.finite_insert s _) ?_
    · simp only [Set.iInter_coe_set, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.iInter_iInter_eq_or_left, Set.iInter_iInter_eq_left, Set.inter_comm t,
        ← Set.inter_assoc, ← Set.subset_empty_iff]
      have : s ∩ InterOfClosedSets U ⊆ s₂ := by
        simp only [← h, Set.inter_union_distrib_left, hss₁, Set.empty_union, Set.inter_subset_right]
      exact (Set.inter_subset_inter this fun _ h ↦ h).trans <| Set.subset_empty_iff.2 <|
        (s₂.inter_comm t).trans hts₂

omit R in
include hU hV in
lemma exists_forall_inter_of_union_eq [Nonempty X] [CompactSpace X]
    [QuasiSeparatedSpace X] {s₁ s₂ : Set X} (h : s₁ ∪ s₂ = InterOfClosedSets U) :
    ∃ t : ({s₁, s₂} : Set (Set X)), ∀ s : U.carrier, s.1 ∩ t.1 ≠ ∅ := by
  refine Or.elim (forall_inter_or_forall_inter_of_union_eq hV hU h) ?_ ?_
  · intro hs₁
    use ⟨s₁, Set.mem_insert _ _⟩
  · intro hs₂
    use ⟨s₂, Set.mem_insert_of_mem _ rfl⟩

omit R in
include hV in
def FICSSOfUnionEq [Nonempty X] [CompactSpace X] [QuasiSeparatedSpace X]
    {s₁ s₂ : Set X} (h : s₁ ∪ s₂ = InterOfClosedSets U)
    (s₁_closed : IsClosed s₁) (s₂_closed : IsClosed s₂)
    (s₁_nonempty : s₁.Nonempty) (s₂_nonempty : s₂.Nonempty):
    FiniteInterClosedSubbasisSet V where
  carrier := U.carrier ∪ { (exists_forall_inter_of_union_eq hV hU h).choose.1 }
  forall_mem := by
    intro s
    have mem := s.2
    simp only [Set.union_singleton] at mem
    refine Or.elim mem ?_ ?_
    · intro eq
      rw [hV, eq]
      refine Or.intro_left _ ?_
      · refine Or.elim (exists_forall_inter_of_union_eq hV hU h).choose.2 ?_ ?_
        · intro eq1
          simpa only [Subtype.forall] using Set.mem_of_eq_of_mem eq1 s₁_closed
        · intro eq2
          simpa only [Subtype.forall] using Set.mem_of_eq_of_mem eq2 s₂_closed
    · intro hsU
      exact U.forall_mem ⟨s, hsU⟩
  finite_inter := by
    intro T' subset nonempty finite
    by_cases hT' : (exists_forall_inter_of_union_eq hV hU h).choose.1 ∈ T'
    · have h1 : T' = (T' ∩ U.carrier) ∪
          { (exists_forall_inter_of_union_eq hV hU h).choose.1 } := by
        ext
        simp only [Set.union_singleton]
        constructor
        · intro hsT'
          exact Or.elim (subset hsT') (fun h => Or.intro_right _ ⟨hsT', h⟩) (fun h => Or.inl h)
        · intro hsTU'
          exact Or.elim hsTU' (fun h => Set.mem_of_eq_of_mem h hT')
            (fun h => Set.mem_of_mem_inter_right h.symm)
      have h2 : T' ∩ U.carrier = ((T' ∩ U.carrier) ∩ { s | IsClosed s }) ∪
          ((T' ∩ U.carrier) ∩ { s | IsOpen s ∧ IsCompact s }) := by
        rw [← Set.inter_union_distrib_left, ← hV, Set.inter_assoc,
          Set.inter_eq_left.2 (fun s hs => U.forall_mem ⟨s, hs⟩)]
      have h3 : (exists_forall_inter_of_union_eq hV hU h).choose.1 ⊆
          ⋂ s ∈ T' ∩ U.carrier ∩ { s | IsClosed s }, s := by
        intro x
        refine Or.elim (exists_forall_inter_of_union_eq hV hU h).choose.2 ?_ ?_
        · intro eq mem
          rw [eq] at mem
          simp only [Set.mem_inter_iff, Set.mem_iInter, and_imp]
          have : s₁ ⊆ InterOfClosedSets U := by
            rw [← h]
            exact Set.subset_union_left
          have := this mem
          simp only [InterOfClosedSets, Set.mem_sInter, Set.mem_inter_iff, and_imp] at this
          intro s hsT' hsU hs
          exact this s hsU hs
        · intro eq mem
          rw [eq] at mem
          simp only [Set.mem_inter_iff, Set.mem_iInter, and_imp]
          have : s₂ ⊆ InterOfClosedSets U := by
            rw [← h]
            exact Set.subset_union_right
          have := this mem
          simp only [InterOfClosedSets, Set.mem_sInter, Set.mem_inter_iff, and_imp] at this
          intro s hsT' hsU hs
          exact this s hsU hs
      rw [h1]
      simp only [Set.iInter_coe_set, Set.union_singleton, Set.mem_insert_iff,
        Set.iInter_iInter_eq_or_left]
      rw [h2, Set.biInter_union, ← Set.inter_assoc, Set.inter_eq_left.2 h3]
      by_cases empty : (T' ∩ U.carrier ∩ { S | IsOpen S ∧ IsCompact S } : Set (Set X)) = ∅
      · have : (exists_forall_inter_of_union_eq hV hU h).choose.1.Nonempty := by
          refine Or.elim (exists_forall_inter_of_union_eq hV hU h).choose.2 ?_ ?_
          · intro eq
            rw [eq]
            exact s₁_nonempty
          · intro eq
            rw [eq]
            exact s₂_nonempty
        simpa only [empty, Set.mem_empty_iff_false, Set.iInter_of_empty, Set.iInter_univ,
          Set.inter_univ] using Set.nonempty_iff_ne_empty.mp this
      · have : ⋂ s ∈ T' ∩ U.carrier ∩ { s | IsOpen s ∧ IsCompact s }, s ∈ U.carrier := by
          refine sInter_of_oc_sets_mem hV hU ?_ Set.inter_subset_right ?_ ?_
          · rw [Set.inter_comm, ← Set.inter_assoc]
            exact Set.inter_subset_right
          · exact Set.nonempty_iff_ne_empty'.mpr empty
          · rw [Set.inter_assoc]
            exact Finite.Set.finite_inter_of_left T' _
        rw [Set.inter_comm]
        exact Set.nonempty_iff_ne_empty'.mp <| Set.Nonempty.coe_sort <| Set.nonempty_iff_ne_empty.2
          <| (exists_forall_inter_of_union_eq hV hU h).choose_spec ⟨_, this⟩
    · have : T' ⊆ U.carrier := by
        simp only [Set.union_singleton] at subset
        exact (Set.subset_insert_iff_of_not_mem hT').mp subset
      exact U.finite_inter T' this nonempty finite

omit R in
include hU hV in
lemma isIrreducible [Nonempty X] [CompactSpace X] [QuasiSeparatedSpace X] :
    IsIrreducible (InterOfClosedSets U) := by
  fconstructor
  · exact nonempty U
  · by_contra h
    simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or,
      exists_and_left] at h
    obtain ⟨C1, not_subset1, C2, closed1, closed2, subset, not_subset2⟩ := h
    have eq_union : InterOfClosedSets U =
        ((InterOfClosedSets U) ∩ C1) ∪ ((InterOfClosedSets U) ∩ C2) := by
      rw [← Set.inter_union_distrib_left]
      exact Set.left_eq_inter.mpr subset
    have nonempty1 : ((InterOfClosedSets U) ∩ C1).Nonempty := by
      by_contra h1
      rw [Set.not_nonempty_iff_eq_empty.mp h1, Set.empty_union, Set.left_eq_inter] at eq_union
      exact not_subset2 eq_union
    have nonempty2 : ((InterOfClosedSets U) ∩ C2).Nonempty := by
      by_contra h2
      rw [Set.not_nonempty_iff_eq_empty.mp h2, Set.union_empty, Set.left_eq_inter] at eq_union
      exact not_subset1 eq_union
    have mem : (exists_forall_inter_of_union_eq hV hU eq_union.symm).choose.1 ∈ U.carrier := by
      by_contra h
      have lt : U < FICSSOfUnionEq hV hU eq_union.symm (IsClosed.inter (isClosed U) closed1)
          (IsClosed.inter (isClosed U) closed2) nonempty1 nonempty2 := by
        refine lt_of_le_of_ne ?_ ?_
        · intro s hs
          exact Set.mem_union_left _ hs
        · intro eq
          simp_rw [congrArg carrier eq, FICSSOfUnionEq] at h
          simp only [Set.union_singleton, Set.mem_insert_iff, true_or, not_true_eq_false] at h
      exact not_le_of_lt lt <| hU <| le_of_lt lt
    have lt : (exists_forall_inter_of_union_eq hV hU eq_union.symm).choose.1 <
        InterOfClosedSets U := by
      refine Or.elim (exists_forall_inter_of_union_eq hV hU eq_union.symm).choose.2 ?_ ?_
      · intro eq
        rw [eq]
        refine lt_of_le_of_ne Set.inter_subset_left ?_
        · intro eq
          rw [← eq] at not_subset1
          exact not_subset1 Set.inter_subset_right
      · intro eq
        rw [eq]
        refine lt_of_le_of_ne Set.inter_subset_left ?_
        · intro eq
          rw [← eq] at not_subset2
          exact not_subset2 Set.inter_subset_right
    have le : InterOfClosedSets U ≤
        (exists_forall_inter_of_union_eq hV hU eq_union.symm).choose.1 := by
      intro x
      simp only [InterOfClosedSets, Set.mem_sInter, Set.mem_inter_iff, and_imp, Subtype.forall]
      intro hx
      have : IsClosed (exists_forall_inter_of_union_eq hV hU eq_union.symm).choose.1 := by
        refine Or.elim (exists_forall_inter_of_union_eq hV hU eq_union.symm).choose.2 ?_ ?_
        · intro eq
          rw [eq]
          exact IsClosed.inter (isClosed U) closed1
        · intro eq
          rw [eq]
          exact IsClosed.inter (isClosed U) closed2
      simp only [Subtype.forall] at mem this
      exact hx _ mem this
    exact not_le_of_lt lt le

omit R in
include hU hV in
lemma mem_of_isGenericPoint [Nonempty X] [CompactSpace X] [QuasiSeparatedSpace X]
    {x : X} (hx : IsGenericPoint x (InterOfClosedSets U)) (s : U.carrier) :
    x ∈ s.1 := by
  have := U.forall_mem
  rw [hV] at this
  refine Or.elim (this s) ?_ ?_
  · intro hs
    have : InterOfClosedSets U ⊆ s.1 := by
      intro x
      simp only [InterOfClosedSets, Set.mem_sInter, Set.mem_inter_iff, and_imp]
      intro hx
      exact hx s s.2 hs
    exact this <| IsGenericPoint.mem hx
  · rintro ⟨hs1, hs2⟩
    by_contra not_mem
    have neq : InterOfClosedSets U ∩ s ≠ ∅ := by
      have : { InterOfClosedSets U, s.1 } ⊆ U.carrier := by
        intro t ht
        refine Or.elim ht ?_ ?_
        · intro eq
          rw [eq]
          exact mem_carrier hV hU
        · intro eq
          rw [eq]
          exact s.2
      simpa only [Set.iInter_coe_set, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.iInter_iInter_eq_or_left, Set.iInter_iInter_eq_left] using
          U.finite_inter { InterOfClosedSets U, s.1 } this (Set.instNonemptyElemInsert _ _)
          (Finite.Set.finite_insert _ _)
    have le : InterOfClosedSets U ≤ InterOfClosedSets U \ s := by
      nth_rw 1 [← hx]
      refine (IsClosed.mem_iff_closure_subset ?_).1 ?_
      · exact IsClosed.inter (isClosed U) (isClosed_compl_iff.mpr hs1)
      · exact ⟨IsGenericPoint.mem hx, not_mem⟩
    have lt : InterOfClosedSets U \ s < InterOfClosedSets U := by
      simp only [Set.lt_eq_ssubset, Set.diff_ssubset_left_iff]
      exact Set.nonempty_iff_ne_empty.mpr neq
    exact not_lt_of_le le lt

end InterOfClosedSets
