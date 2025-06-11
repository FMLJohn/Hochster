import Mathlib.Topology.Constructible
import Mathlib.Topology.Spectral.Basic

open TopologicalSpace Topology

theorem latticeClosure.sup_inf_induction {α : Type*} [Lattice α]
    {s : Set α} (p : (a : α) → a ∈ latticeClosure s → Prop)
    (mem : ∀ (a : α) (has : a ∈ s), p a (subset_latticeClosure has))
    (sup : ∀ (a : α) (has : a ∈ latticeClosure s) (b : α) (hbs : b ∈ latticeClosure s),
      p a has → p b hbs → p (a ⊔ b) (IsSublattice.supClosed isSublattice_latticeClosure has hbs))
    (inf : ∀ (a : α) (has : a ∈ latticeClosure s) (b : α) (hbs : b ∈ latticeClosure s),
      p a has → p b hbs → p (a ⊓ b) (IsSublattice.infClosed isSublattice_latticeClosure has hbs))
    {a : α} (has : a ∈ latticeClosure s) :
    p a has := by
  have h1 : s ⊆ { a : α | ∃ has : a ∈ latticeClosure s, p a has } := by
    intro a ha
    exact ⟨subset_latticeClosure ha, mem a ha⟩
  have h2 : IsSublattice { a : α | ∃ has : a ∈ latticeClosure s, p a has } := {
    supClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨IsSublattice.supClosed isSublattice_latticeClosure has hbs, sup a has b hbs hpa hpb⟩
    infClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨IsSublattice.infClosed isSublattice_latticeClosure has hbs, inf a has b hbs hpa hpb⟩ }
  exact (latticeClosure_min h1 h2 has).choose_spec

lemma Set.compl_image_latticeClosure {X : Type*} (S : Set (Set X)) :
    compl '' (latticeClosure S) = latticeClosure (compl '' S) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro s ⟨c, hcS, hcs⟩
    refine hcs ▸ latticeClosure.sup_inf_induction (fun c hcS => cᶜ ∈ latticeClosure (compl '' S))
      ?_ ?_ ?_ hcS
    · intro c hcS
      exact subset_latticeClosure <| Set.mem_image_of_mem compl hcS
    · intro a _ b _ haS hbS
      exact Set.compl_union _ _ ▸ IsSublattice.infClosed isSublattice_latticeClosure haS hbS
    · intro a _ b _ haS hbS
      exact Set.compl_inter _ _ ▸ IsSublattice.supClosed isSublattice_latticeClosure haS hbS
  · refine latticeClosure_min ?_ ?_
    · intro s ⟨c, hcS, hcs⟩
      exact ⟨c, subset_latticeClosure hcS, hcs⟩
    · exact {
      supClosed := fun a ⟨c, hcS, hca⟩ b ⟨d, hdS, hdb⟩ =>
        ⟨aᶜ ⊓ bᶜ, hca ▸ hdb ▸ IsSublattice.infClosed isSublattice_latticeClosure
          ((compl_compl c).symm ▸ hcS) ((compl_compl d).symm ▸ hdS),
            Set.compl_inter _ _ ▸ (compl_compl a).symm ▸ (compl_compl b).symm ▸ rfl⟩
      infClosed := fun a ⟨c, hcS, hca⟩ b ⟨d, hdS, hdb⟩ =>
        ⟨aᶜ ⊔ bᶜ, hca ▸ hdb ▸ IsSublattice.supClosed isSublattice_latticeClosure
          ((compl_compl c).symm ▸ hcS) ((compl_compl d).symm ▸ hdS),
            Set.compl_union _ _ ▸ (compl_compl a).symm ▸ (compl_compl b).symm ▸ rfl⟩ }

lemma Set.compl_image_latticeClosure_eq_of_compl_image_eq_self
    {X : Type*} {S : Set (Set X)} (hS : compl '' S = S) :
    compl '' (latticeClosure S) = latticeClosure S :=
  Set.compl_image_latticeClosure S ▸ hS.symm ▸ rfl

lemma TopologicalSpace.generateFrom_latticeClosure {X : Type*} (S : Set (Set X)) :
    generateFrom (latticeClosure S) = generateFrom S := by
  refine eq_of_le_of_le ?_ ?_
  · refine le_generateFrom ?_
    · intro o hoS
      exact isOpen_generateFrom_of_mem <| subset_latticeClosure hoS
  · refine le_generateFrom ?_
    · intro o hoS
      refine latticeClosure.sup_inf_induction (fun s _ => IsOpen[generateFrom S] s) ?_ ?_ ?_ hoS
      · intro _ h
        exact isOpen_generateFrom_of_mem h
      · intro _ _ _ _ h1 h2
        exact @IsOpen.union X _ _ (generateFrom S) h1 h2
      · intro _ _ _ _ h1 h2
        exact @IsOpen.inter X (generateFrom S) _ _ h1 h2

lemma TopologicalSpace.generateFrom_booleanSubalgebra_closure_eq_of_isSublattice {X : Type*}
    {S : Set (Set X)} (hS1 : ⊥ ∈ S) (hS2 : compl '' S = S) (hS3 : IsSublattice S) :
    generateFrom (BooleanSubalgebra.closure S) = generateFrom S := by
  refine eq_of_le_of_le ?_ ?_
  · refine le_generateFrom ?_
    · intro _ h
      exact isOpen_generateFrom_of_mem <| BooleanSubalgebra.subset_closure h
  · refine le_generateFrom ?_
    · intro s hsS
      refine BooleanSubalgebra.closure_sdiff_sup_induction hS3 hS1 (hS2 ▸ ⟨⊥, hS1, compl_bot⟩)
        ?_ ?_ s hsS
      · intro s hsS t htS
        exact Set.diff_eq_compl_inter ▸
          (isOpen_generateFrom_of_mem <| IsSublattice.infClosed hS3
            (hS2 ▸ Set.mem_image_of_mem compl htS) hsS)
      · intro _ _ _ _ h1 h2
        exact @IsOpen.union _ _ _ (generateFrom S) h1 h2

lemma TopologicalSpace.generateFrom_booleanSubalgebra_closure
    {X : Type*} {S : Set (Set X)} (hS1 : ⊥ ∈ S) (hS2 : compl '' S = S) :
    generateFrom (BooleanSubalgebra.closure S) = generateFrom S :=
  BooleanSubalgebra.closure_latticeClosure S ▸
    generateFrom_booleanSubalgebra_closure_eq_of_isSublattice (subset_latticeClosure hS1)
      (Set.compl_image_latticeClosure_eq_of_compl_image_eq_self hS2) isSublattice_latticeClosure ▸
        generateFrom_latticeClosure S

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [QuasiSeparatedSpace X]

lemma TopologicalSpace.generateFrom_isConstructible_eq_generateFrom_union_compl_image :
    generateFrom { s : Set X | IsConstructible s } =
    generateFrom ({ s | IsOpen s ∧ IsCompact s } ∪ compl '' { s | IsOpen s ∧ IsCompact s }) := by
  have h1 : ⊥ ∈ { s : Set X | IsOpen s ∧ IsCompact s } ∪ compl '' { s | IsOpen s ∧ IsCompact s } :=
    Or.intro_left _ ⟨isOpen_empty, isCompact_empty⟩
  have h2 : compl '' ({ s | IsOpen s ∧ IsCompact s } ∪ compl '' { s | IsOpen s ∧ IsCompact s }) =
      { s : Set X | IsOpen s ∧ IsCompact s } ∪ compl '' { s | IsOpen s ∧ IsCompact s } :=
    (Set.image_union _ _ _).symm ▸
      (Set.compl_compl_image { s : Set X | IsOpen s ∧ IsCompact s }).symm ▸
        Set.union_comm _ _
  refine generateFrom_booleanSubalgebra_closure h1 h2 ▸ ?_
  · congr
    refine Set.eq_of_subset_of_subset ?_ ?_
    · refine BooleanSubalgebra.closure_mono ?_
      · intro s ⟨hs1, hs2⟩
        exact Or.intro_left _ ⟨hs1, (QuasiSeparatedSpace.isRetrocompact_iff_isCompact hs1).1 hs2⟩
    · intro s hs
      simp only [Set.mem_setOf_eq]
      refine BooleanSubalgebra.mem_closure.1 hs ?_
      · intro t ht
        refine Or.elim ht ?_ ?_
        · intro ⟨ht1, ht2⟩
          exact BooleanSubalgebra.subset_closure ⟨ht1,
            (QuasiSeparatedSpace.isRetrocompact_iff_isCompact ht1).2 ht2⟩
        · intro ⟨u, ⟨hu1, hu2⟩, hut⟩
          exact hut ▸ BooleanSubalgebra.compl_mem <| BooleanSubalgebra.subset_closure
            ⟨hu1, (QuasiSeparatedSpace.isRetrocompact_iff_isCompact hu1).2 hu2⟩
