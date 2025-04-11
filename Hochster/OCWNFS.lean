import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Defs.Basic

universe u
variable (X : Type u) [TopologicalSpace X]

namespace TopologicalSpace

/--
A cover of a topological space `X` is a collection of subsets of `X` that cover `X`.
-/
structure Cover where
  ι : Type u
  toFun : ι → Set X
  covers : ⋃ i : ι, toFun i = Set.univ

/--
The type of open covers of `X`.
-/
structure OpenCover extends Cover X where
  forall_isOpen : ∀ i : ι, IsOpen (toFun i)

namespace Cover

instance instPreorder : Preorder (Cover X) where
  le := fun U V => { U.toFun i | i : U.ι } ≤ { V.toFun i | i : V.ι }
  lt := fun U V => { U.toFun i | i : U.ι } < { V.toFun i | i : V.ι }
  le_refl := fun _ => fun _ s => s
  le_trans := fun _ _ _ hUV hVW => fun _ s => hVW (hUV s)
  lt_iff_le_not_le := fun _ _ => Eq.to_iff rfl

variable {X} in
/--
Given `U V : Cover X`, `Subcover U V` means that `U` is a subcover of `V`.
-/
def Subcover (U V : Cover X) := U ≤ V

variable {X} in
/--
The cover we obtain by adding a subset of `X` to a cover.
-/
def insert (s : Set X) (U : Cover X) : Cover X where
  ι := (U.toFun '' ⊤).union {s}
  toFun := fun i => i.1
  covers := by
    ext x
    have : x ∈ ⋃ i : U.ι, U.toFun i := by
      rw [U.covers]
      exact trivial
    simp only [Set.top_eq_univ, Set.iUnion_coe_set, Set.image_univ, Set.mem_iUnion, exists_prop,
      Set.mem_univ, iff_true] at this ⊢
    rcases this with ⟨i, hi⟩
    use U.toFun i
    exact ⟨Set.mem_union_left {s} <| Set.mem_range_self i, hi⟩

variable {X} in
omit [TopologicalSpace X] in
lemma subcover_insert (s : Set X) (U : Cover X) : Subcover U (U.insert s) := by
  intro s' hs'
  simp only [insert, Set.top_eq_univ, Subtype.exists, Set.image_univ, exists_prop,
    exists_eq_right] at hs' ⊢
  rcases hs' with ⟨i, hi⟩
  rw [← hi]
  exact Set.mem_union_left {s} <| Set.mem_range_self i

variable {X} in
omit [TopologicalSpace X] in
lemma le_insert (s : Set X) (U : Cover X) : U ≤ (U.insert s) := subcover_insert s U

variable {X} in
omit [TopologicalSpace X] in
lemma lt_insert {s : Set X} {U : Cover X} (hsU : s ∉ U.toFun '' ⊤) : U < (U.insert s) := by
  rw [lt_iff_le_not_le]
  constructor
  · exact le_insert s U
  · intro hle
    exact hsU <| by
      simpa only [Set.top_eq_univ, Set.image_univ] using hle <| by
        simpa only [insert, Cover.insert, Subtype.exists, exists_prop, exists_eq_right] using
          Set.mem_union_right _ rfl

variable {X} in
/--
Given a collection of covers of `X`, the union of them is again a cover.
-/
def iUnion (S : Set (Cover X)) [Nonempty S] : Cover X where
  ι := ⋃ U : S, { (U : Cover X).toFun i | i : (U : Cover X).ι }
  toFun := fun O => O.1
  covers := by
    ext x
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, Set.iUnion_exists,
      Set.biUnion_and', Set.iUnion_iUnion_eq', Set.mem_univ, iff_true]
    use @Classical.ofNonempty S _
    constructor
    · exact Subtype.coe_prop _
    · exact Set.mem_iUnion.mp <| by rw [(@Classical.ofNonempty S _).1.covers]; exact trivial

end Cover

namespace OpenCover

instance instPreorder : Preorder (OpenCover X) where
  le := fun U V => { U.toFun i | i : U.ι } ≤ { V.toFun i | i : V.ι }
  lt := fun U V => { U.toFun i | i : U.ι } < { V.toFun i | i : V.ι }
  le_refl := fun _ => fun _ s => s
  le_trans := fun _ _ _ hUV hVW => fun _ s => hVW (hUV s)
  lt_iff_le_not_le := fun _ _ => Eq.to_iff rfl

variable {X} in
/--
The open cover we obtain by adding an open subset of `X` to an open cover.
-/
def insert {s : Set X} (hs : IsOpen s) (U : OpenCover X) : OpenCover X where
  __ := Cover.insert s U.1
  forall_isOpen := by
    intro i
    simp only [Cover.insert]
    refine' Or.elim ((Set.mem_union i.1 _ _).1 i.2) ?_ ?_
    · rintro ⟨j, _, hj⟩
      rw [← hj]
      exact U.forall_isOpen j
    · intro h
      rw [Set.eq_of_mem_singleton h]
      exact hs

variable {X} in
lemma le_insert {s : Set X} (hs : IsOpen s) (U : OpenCover X) : U ≤ (U.insert hs) := by
  intro s' hs'
  rcases hs' with ⟨i, hi⟩
  simp only [← hi, OpenCover.insert, Cover.insert, Set.top_eq_univ, Subtype.exists, Set.image_univ,
    exists_prop, exists_eq_right]
  exact Set.mem_union_left {s} <| Set.mem_range_self i

lemma lt_insert {s : Set X} (hs : IsOpen s) {U : OpenCover X} (hsU : s ∉ U.toFun '' ⊤) :
    U < (U.insert hs) := by
  rw [lt_iff_le_not_le]
  constructor
  · exact le_insert hs U
  · intro hle
    exact hsU <| by
      simpa only [Set.top_eq_univ, Set.image_univ] using hle <| by
        simpa only [insert, Cover.insert, Subtype.exists, exists_prop, exists_eq_right] using
          Set.mem_union_right _ rfl

end OpenCover

/--
The type of covers of `X` with no finite subcover.
-/
structure CoverWithNoFiniteSubcover extends Cover X where
  not_exists : ¬∃ V : Cover X, Finite V.ι ∧ Cover.Subcover V ⟨ι, toFun, covers⟩

instance CoverWithNoFiniteSubcover.instPreorder : Preorder (CoverWithNoFiniteSubcover X) where
  le := fun U V => { U.toFun i | i : U.ι } ≤ { V.toFun i | i : V.ι }
  lt := fun U V => { U.toFun i | i : U.ι } < { V.toFun i | i : V.ι }
  le_refl := fun _ => fun _ s => s
  le_trans := fun _ _ _ hUV hVW => fun _ s => hVW (hUV s)
  lt_iff_le_not_le := fun _ _ => Eq.to_iff rfl

/--
The type of open covers of `X` with no finite subcover.
-/
structure OpenCoverWithNoFiniteSubcover extends OpenCover X, CoverWithNoFiniteSubcover X where

namespace OpenCoverWithNoFiniteSubcover

instance instPreorder : Preorder (OpenCoverWithNoFiniteSubcover X) where
  le := fun U V => { U.toFun i | i : U.ι } ≤ { V.toFun i | i : V.ι }
  lt := fun U V => { U.toFun i | i : U.ι } < { V.toFun i | i : V.ι }
  le_refl := fun _ => fun _ s => s
  le_trans := fun _ _ _ hUV hVW => fun _ s => hVW (hUV s)
  lt_iff_le_not_le := fun _ _ => Eq.to_iff rfl

variable {X}

lemma nonempty_of_not_compactSpace (h : ¬CompactSpace X) :
    Nonempty (OpenCoverWithNoFiniteSubcover X) := by
  have not_isCompact : ¬IsCompact Set.univ := fun c => h ((@isCompact_univ_iff X _).1 c)
  simp only [isCompact_iff_finite_subcover, Set.univ_subset_iff, not_forall] at not_isCompact
  rcases not_isCompact with ⟨ι, toFun, forall_isOpen, covers, not_exists⟩
  constructor; fconstructor
  · exact ⟨⟨ι, toFun, covers⟩, forall_isOpen⟩
  · simp only [_root_.not_exists, not_and]
    intro U hU1 hU2
    change { U.toFun i | i : U.ι } ⊆ { toFun i | i : ι } at hU2
    have forall_exists (i : U.ι) : ∃ j : ι, U.toFun i = toFun j := by
      simp only [Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff] at hU2
      obtain ⟨j, hj⟩ := hU2 i
      use j
      exact hj.symm
    have finite : Finite ((fun i => (forall_exists i).choose) '' ⊤) :=
      Finite.Set.finite_image ⊤ fun i => (forall_exists i).choose
    have : ⋃ i ∈ Set.Finite.toFinset finite, toFun i = Set.univ := by
      rw [← U.covers]
      ext
      simp only [Set.top_eq_univ, Set.image_univ, Set.Finite.mem_toFinset, Set.mem_range,
        Set.iUnion_exists, Set.iUnion_iUnion_eq', Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        use i
        rw [(forall_exists i).choose_spec]
        exact hi
      · rintro ⟨i, hi⟩
        use i
        rw [← (forall_exists i).choose_spec]
        exact hi
    exact not_exists ⟨Set.Finite.toFinset finite, this⟩

lemma isEmpty_of_compactSpace (h : CompactSpace X) :
    IsEmpty (OpenCoverWithNoFiniteSubcover X) := by
  let is_compact : IsCompact ⊤ := (@isCompact_univ_iff X _).2 h
  simp only [isCompact_iff_finite_subcover, Set.top_eq_univ, Set.univ_subset_iff] at is_compact
  constructor
  intro U
  have := is_compact U.toFun U.forall_isOpen U.covers
  refine U.not_exists ⟨?_, ?_⟩
  · exact {
    ι := this.choose
    toFun := fun i => U.toFun i
    covers := by
      have heq : ⋃ i ∈ this.choose, U.toFun i = ⋃ i : { i // i ∈ this.choose }, U.toFun i := by
        ext
        simp only [Set.mem_iUnion, Subtype.exists]
      rw [← heq]
      exact this.choose_spec }
  · constructor
    · exact Finite.of_fintype _
    · intro _ ⟨i, hi⟩
      use i

variable (X) in
lemma isEmpty_iff_compactSpace :
    IsEmpty (OpenCoverWithNoFiniteSubcover X) ↔ CompactSpace X := by
  constructor
  · contrapose
    simp only [not_isEmpty_iff]
    exact fun h ↦ nonempty_of_not_compactSpace h
  · exact fun h ↦ isEmpty_of_compactSpace h

/--
If `X` is nonempty, then given any nonempty chain `C` with elements in
`OpenCoverWithNoFiniteSubcover X`, the union of elements of `C` forms an open cover of `X` with no
finite subcover.
-/
def chainIUnion [Nonempty X] {C : Set (OpenCoverWithNoFiniteSubcover X)} [Nonempty C]
    (hC : IsChain (fun U V => U ≤ V) C) : OpenCoverWithNoFiniteSubcover X where
  ι := ⋃ U : C, { U.1.toFun i | i : U.1.ι }
  toFun := fun O => O.1
  covers := by
    ext x
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, Set.iUnion_exists,
      Set.biUnion_and', Set.iUnion_iUnion_eq', Set.mem_univ, iff_true]
    use @Classical.ofNonempty C _
    constructor
    · exact Subtype.coe_prop _
    · exact Set.mem_iUnion.mp <| by rw [(@Classical.ofNonempty C _).1.covers]; exact trivial
  forall_isOpen := by
    rintro ⟨O, hO⟩
    simp only [Set.iUnion_coe_set, Set.mem_iUnion] at hO ⊢
    obtain ⟨U, hU1, ⟨i, hi⟩⟩ := hO
    rw [← hi]
    exact U.forall_isOpen i
  not_exists := by
    by_contra h
    obtain ⟨V, hV1, hV2⟩ := h
    change { V.toFun i | i : V.ι } ≤ _ at hV2
    simp only [Subtype.exists, Set.mem_iUnion, exists_prop, exists_eq_right, Set.le_eq_subset,
      Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff] at hV2
    haveI : Nonempty V.ι := by
      by_contra h
      simp only [not_nonempty_iff] at h
      let hV := V.covers
      simp only [Set.iUnion_of_empty] at hV
      exact (not_nonempty_iff.mpr <| Set.univ_eq_empty_iff.mp hV.symm) inferInstance
    have subset : (fun i => (hV2 i).choose) '' ⊤ ⊆ C := by
      intro U hU
      simp only [Set.top_eq_univ, Set.image_univ] at hU
      rw [← hU.choose_spec]
      exact (hV2 hU.choose).choose_spec.1
    have exists_isMax : ∃ m : (fun i => (hV2 i).choose) '' ⊤, IsMax m := by
      by_contra h
      simp only [Subtype.exists, _root_.not_exists, not_isMax_iff] at h
      haveI : Infinite ((fun i => (hV2 i).choose) '' ⊤) := by
        refine @NoMaxOrder.infinite ((fun i => (hV2 i).choose) '' ⊤) _
          (Set.instNonemptyElemImage _ ⊤) ?_
        · constructor
          intro U
          obtain ⟨W, hW, hW1, hW2⟩ := h U U.2
          use ⟨W, hW⟩
          exact lt_of_le_not_le hW1 hW2
      exact not_finite ((fun i => (hV2 i).choose) '' ⊤)
    have exists_le : ∃ U ∈ C, V ≤ U.1.1 := by
      use exists_isMax.choose
      constructor
      · exact subset <| Subtype.coe_prop exists_isMax.choose
      · change { V.toFun i | i : V.ι } ⊆ _
        simp only [Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff]
        intro i
        have mem : (hV2 i).choose ∈ (fun i => (hV2 i).choose) '' ⊤ := by
          simp only [Set.top_eq_univ, Set.image_univ]
          use i
        have le : (hV2 i).choose ≤ exists_isMax.choose :=
          (IsChain.not_lt (IsChain.mono subset hC) exists_isMax.choose.2 mem).1 <|
            isMax_iff_forall_not_lt.1 exists_isMax.choose_spec ⟨_, mem⟩
        change { (hV2 i).choose.toFun j | j : (hV2 i).choose.ι } ⊆ _ at le
        simp only [Set.setOf_subset_setOf, forall_exists_index, forall_apply_eq_imp_iff] at le
        rw [← (hV2 i).choose_spec.2.choose_spec]
        exact le (Exists.choose_spec (hV2 i)).right.choose
    exact exists_le.choose.2 ⟨V, hV1, exists_le.choose_spec.2⟩

lemma le_chainIUnion [Nonempty X] {C : Set (OpenCoverWithNoFiniteSubcover X)} [Nonempty C]
    (hC : IsChain (fun U V => U ≤ V) C) (U : C) : U ≤ chainIUnion hC := by
  intro O hO
  unfold chainIUnion
  simp only [Subtype.exists, Set.mem_iUnion, exists_prop, exists_eq_right]
  exact ⟨U, Subtype.coe_prop U, hO⟩

lemma exists_isMax_of_nonempty_of_not_compactSpace [Nonempty X] (h : ¬CompactSpace X) :
    ∃ U : OpenCoverWithNoFiniteSubcover X, IsMax U := by
  haveI : Nonempty (OpenCoverWithNoFiniteSubcover X) := nonempty_of_not_compactSpace h
  refine zorn_le_nonempty ?_
  · intro C hC1 hC2
    haveI : Nonempty C := Set.Nonempty.to_subtype hC2
    exact ⟨chainIUnion hC1, fun U hUC => le_chainIUnion hC1 ⟨U, hUC⟩⟩

/--
A maximal element in `OpenCoverWithNoFiniteSubcover X`, when `X` is neither empty nor compact.
-/
noncomputable def Max [Nonempty X] (h : ¬CompactSpace X) : OpenCoverWithNoFiniteSubcover X :=
  (exists_isMax_of_nonempty_of_not_compactSpace h).choose

lemma max_isMax [Nonempty X] (h : ¬CompactSpace X) : IsMax (Max h) :=
  (exists_isMax_of_nonempty_of_not_compactSpace h).choose_spec

lemma max_not_lt [Nonempty X] (h : ¬CompactSpace X) (U : OpenCoverWithNoFiniteSubcover X) :
    ¬(Max h) < U := IsMax.not_lt <| max_isMax h

lemma exists_finite_subcover_of_not_mem [Nonempty X] (h : ¬CompactSpace X)
    {s : Set X} (hs : IsOpen s) (hs1 : s ∉ (Max h).toFun '' ⊤) :
    ∃ V : Cover X, Finite V.ι ∧ Cover.Subcover V ((Max h).insert hs).1 := by
  by_contra hn
  let U : OpenCoverWithNoFiniteSubcover X := {
    ι := (OpenCover.insert hs (Max h).toOpenCover).ι
    toFun := (OpenCover.insert hs (Max h).toOpenCover).toFun
    covers := (OpenCover.insert hs (Max h).toOpenCover).covers
    forall_isOpen := (OpenCover.insert hs (Max h).toOpenCover).forall_isOpen
    not_exists := hn
  }
  exact max_not_lt h U <| Cover.lt_insert hs1

/--
`finiteCoverOfNotMem h hs hs1 = (exists_finite_subcover_of_not_mem h hs hs1).choose`.
-/
noncomputable def finiteCoverOfNotMem [Nonempty X] (h : ¬CompactSpace X)
    {s : Set X} (hs : IsOpen s) (hs1 : s ∉ (Max h).toFun '' ⊤) :=
  (exists_finite_subcover_of_not_mem h hs hs1).choose

theorem finiteCoverOfNotMem_ι_finite [Nonempty X] (h : ¬CompactSpace X)
    {s : Set X} (hs : IsOpen s) (hs1 : s ∉ (Max h).toFun '' ⊤) :
    Finite (finiteCoverOfNotMem h hs hs1).ι :=
  (exists_finite_subcover_of_not_mem h hs hs1).choose_spec.1

theorem subcover_finiteCoverOfNotMem_max [Nonempty X] (h : ¬CompactSpace X)
    {s : Set X} (hs : IsOpen s) (hs1 : s ∉ (Max h).toFun '' ⊤) :
    Cover.Subcover (finiteCoverOfNotMem h hs hs1) ((Max h).insert hs).1 :=
  (exists_finite_subcover_of_not_mem h hs hs1).choose_spec.2

open Classical

/--
The union of `{(Max h).toFun i}` and
`⋃ s : S, (finiteCoverOfNotMem h (h1 s) (h2 s)).toFun '' ⊤ \ {s.1}` forms a cover of `X`.
-/
def UnionCover [Nonempty X] (h : ¬CompactSpace X) {i : (Max h).ι} {S : Set (Set X)}
    (h1 : ∀ (s : S), IsOpen s.1) (h2 : ∀ (s : S), s.1 ∉ (Max h).toFun '' ⊤)
    (h3 : ⋂₀ S ⊆ (Max h).toFun i) : Cover X where
  ι := Set.union {(Max h).toFun i}
    (⋃ s : S, (finiteCoverOfNotMem h (h1 s) (h2 s)).toFun '' ⊤ \ {s.1})
  toFun := fun i => i.1
  covers := by
    simp only [Set.top_eq_univ, Set.iUnion_coe_set, Set.image_univ]
    have heq : ⋃ s ∈ Set.union {(Max h).toFun i} (⋃ s : Set X, ⋃ (hs : s ∈ S),
        Set.range (finiteCoverOfNotMem h (h1 ⟨s, hs⟩) (h2 ⟨s, hs⟩)).toFun \ {s}),
        s = ((Max h).toFun i).union (⋃ s : S,
        (⋃ s' : Set.diff ((finiteCoverOfNotMem h (h1 s) (h2 s)).toFun '' ⊤) {s.1}, s')) := by
      ext x
      simp only [Set.mem_iUnion, Set.top_eq_univ, Set.iUnion_coe_set, Set.image_univ]
      constructor
      · rintro ⟨s, hs1, hs2⟩
        refine Or.elim ((Set.mem_union s _ _).1 hs1) ?_ ?_
        · intro hs
          simp only [Set.mem_singleton_iff] at hs
          simpa only [hs] using Set.mem_union_left _ hs2
        · intro hs
          refine Set.mem_union_right _ ?_
          simp only [Set.mem_iUnion] at hs ⊢
          rcases hs with ⟨s', hs', mem⟩
          exact ⟨s', hs', s, mem, hs2⟩
      · intro hx
        simp only [exists_prop]
        refine Or.elim ((Set.mem_union x _ _).1 hx) ?_ ?_
        · intro hx
          exact ⟨(Max h).toFun i, Set.mem_union_left _ rfl, hx⟩
        · intro hx
          simp only [Set.mem_iUnion] at hx ⊢
          obtain ⟨s, hs, s', hs'1, hs'2⟩ := hx
          use s'
          constructor
          · refine Set.mem_union_right _ ?_
            simpa only [Set.mem_iUnion] using ⟨s, hs, hs'1⟩
          · exact hs'2
    rw [heq]
    refine @Set.eq_univ_of_subset _ ?_ _ ?_ ?_
    · exact (⋂ s : S, s.1).union
        (⋃ s : S, (⋃ s' : Set.diff ((finiteCoverOfNotMem h (h1 s) (h2 s)).toFun '' ⊤) {s.1}, s'))
    · refine Set.union_subset_union_left _ ?_
      simpa only [Set.sInter_eq_iInter] using h3
    · change _ ∪ _ = _
      simp only [Set.iInter_union, Set.top_eq_univ, Set.iUnion_coe_set, Set.image_univ,
        Set.iInter_coe_set, Set.iInter_eq_univ]
      intro s hs
      ext x
      simp only [Set.mem_union, Set.mem_iUnion, exists_prop, Set.mem_univ, iff_true,
        Decidable.or_iff_not_imp_left]
      intro not_mem
      use s
      use hs
      have : x ∈ ⋃ i, (finiteCoverOfNotMem h (h1 ⟨s, hs⟩) (h2 ⟨s, hs⟩)).toFun i := by
        rw [(finiteCoverOfNotMem h (h1 ⟨s, hs⟩) (h2 ⟨s, hs⟩)).covers]
        exact trivial
      simp only [Set.mem_iUnion] at this
      rcases this with ⟨j, hj⟩
      use (finiteCoverOfNotMem h (h1 ⟨s, hs⟩) (h2 ⟨s, hs⟩)).toFun j
      constructor
      · change _ ∈ _ \ _
        rw [Set.mem_diff]
        constructor
        · exact Set.mem_range_self j
        · intro hs
          rw [hs] at hj
          exact not_mem hj
      · exact hj

end OpenCoverWithNoFiniteSubcover

end TopologicalSpace
