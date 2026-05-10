import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import UnbalancedHaarWavelet.GridDefinition
import UnbalancedHaarWavelet.HaarWaveletsDefinition

/-!
Algebraic identities for finite linear combinations of Haar wavelets.

The lemmas here give explicit one-step and chain-level formulas for indicators
and normalized indicators, which are later used to prove span and density
results.
-/

namespace UnbalancedHaarWavelet

open scoped BigOperators
open scoped Classical

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- The support of a singleton family of cells is the cell itself. -/
lemma branchSupport_singleton [DecidableEq (Set α)] (s : Set α) :
    branchSupport ({s} : Finset (Set α)) = s := by
  ext x
  simp [branchSupport]

omit [MeasurableSpace α] in
/-- The support of a union of two finite families of cells is the union of the supports. -/
lemma branchSupport_union [DecidableEq (Set α)] (A B : Finset (Set α)) :
    branchSupport (A ∪ B) = branchSupport A ∪ branchSupport B := by
  ext x
  constructor
  · intro hx
    rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
    rcases hs with hsA | hsB
    · exact Or.inl (by
        simpa [branchSupport] using
          (show x ∈ ⋃ t ∈ (A : Set (Set α)), t from
            Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hsA, hxs⟩⟩))
    · exact Or.inr (by
        simpa [branchSupport] using
          (show x ∈ ⋃ t ∈ (B : Set (Set α)), t from
            Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hsB, hxs⟩⟩))
  · intro hx
    rcases hx with hxA | hxB
    · rcases (by simpa [branchSupport] using hxA) with ⟨s, hsA, hxs⟩
      simpa [branchSupport] using
        (show x ∈ ⋃ t ∈ ((A ∪ B : Finset (Set α)) : Set (Set α)), t from
          Set.mem_iUnion.2
            ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inl hsA), hxs⟩⟩)
    · rcases (by simpa [branchSupport] using hxB) with ⟨s, hsB, hxs⟩
      simpa [branchSupport] using
        (show x ∈ ⋃ t ∈ ((A ∪ B : Finset (Set α)) : Set (Set α)), t from
          Set.mem_iUnion.2
            ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inr hsB), hxs⟩⟩)

/-- The union of all children of a grid cell is the cell itself. -/
lemma branchSupport_childrenFinset_eq
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (level : ℕ) (cell : Set α) (hcell : cell ∈ G.grid.partitions level) :
    branchSupport (G.childrenFinset level cell) = cell := by
  ext x
  constructor
  · intro hx
    rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
    have hs_child : s ∈ G.children level cell := (G.mem_childrenFinset_iff level cell s).1 hs
    exact hs_child.2 hxs
  · intro hx
    have hx_children : x ∈ ⋃ s ∈ G.children level cell, s :=
      G.covering_by_children level cell hcell hx
    rcases (by simpa using hx_children) with ⟨s, hs_child, hxs⟩
    have hs_fin : s ∈ G.childrenFinset level cell :=
      (G.mem_childrenFinset_iff level cell s).2 hs_child
    simpa [branchSupport] using
      (show x ∈ ⋃ t ∈ (G.childrenFinset level cell : Set (Set α)), t from
        Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hs_fin, hxs⟩⟩)

/-- For a family of children of a fixed grid cell, a child `s` is contained in the union of
that family iff it is one of its members. -/
lemma child_subset_branchSupport_iff_mem
    (G : Grid (α := α)) [DecidableEq (Set α)]
    {level : ℕ} {cell s : Set α}
    (hs_child : s ∈ G.children level cell)
    {A : Finset (Set α)}
    (hA_childs : ∀ t, t ∈ A → t ∈ G.children level cell) :
    s ⊆ branchSupport A ↔ s ∈ A := by
  constructor
  · intro hs_sub
    obtain ⟨x, hx⟩ := G.partition_nonempty (level + 1) s hs_child.1
    have hx_union : x ∈ branchSupport A := hs_sub hx
    rcases (by simpa [branchSupport] using hx_union) with ⟨t, htA, hxt⟩
    have ht_child : t ∈ G.children level cell := hA_childs t htA
    by_cases hst : s = t
    · simpa [hst] using htA
    · have hdisj : Disjoint s t :=
        G.grid.disjoint (level + 1) s t hs_child.1 ht_child.1 hst
      exact (Set.disjoint_left.mp hdisj hx hxt).elim
  · intro hsA
    exact subset_branchSupport_of_mem hsA

omit [MeasurableSpace α] in
/-- The combinatorial support of a branch cannot be contained in a singleton cell: both
components of a branch are nonempty and disjoint. -/
lemma branch_combinatorialSupport_not_subset_singleton
    [DecidableEq (Set α)]
    {T : BinaryTreeWithRootandTops (Set α)}
    {B : Finset (Set α) × Finset (Set α)}
    (hB : B ∈ T.Branches) (s : Set α) :
    ¬ Combinatorial_Support B ⊆ ({s} : Finset (Set α)) := by
  intro hsub
  obtain ⟨u, hu⟩ := (T.NonemptyPairs B hB).1
  obtain ⟨v, hv⟩ := (T.NonemptyPairs B hB).2
  have hu_support : u ∈ Combinatorial_Support B := by
    dsimp [Combinatorial_Support]
    exact Finset.mem_union_left B.2 hu
  have hv_support : v ∈ Combinatorial_Support B := by
    dsimp [Combinatorial_Support]
    exact Finset.mem_union_right B.1 hv
  have hu_eq : u = s := by
    simpa using hsub hu_support
  have hv_eq : v = s := by
    simpa using hsub hv_support
  have hdisj := T.DisjointComponents B hB
  exact Finset.disjoint_left.mp hdisj hu (by simpa [hu_eq, hv_eq] using hv)

/-- The support of the root branch of the binary refinement tree of a grid cell is the cell. -/
lemma branchSupport_root_eq_cell
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level} :
    branchSupport
      (Combinatorial_Support (H.binaryRefinement.tree level cell hcell).Root) = cell := by
  let T := H.binaryRefinement.tree level cell hcell
  have hroot_childs : Combinatorial_Support T.Root = T.Childs := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset
        (T.TreeStructureChilds T.Root T.RootinBranches).1
        (T.TreeStructureChilds T.Root T.RootinBranches).2
    · exact T.RootcontainsChilds
  have hchilds_finset : T.Childs = G.childrenFinset level cell := by
    ext s
    constructor
    · intro hs
      exact (G.mem_childrenFinset_iff level cell s).2
        ((H.binaryRefinement.childs_are_children level cell hcell s).1 hs)
    · intro hs
      exact (H.binaryRefinement.childs_are_children level cell hcell s).2
        ((G.mem_childrenFinset_iff level cell s).1 hs)
  calc
  /--
  Global sum over all ancestor levels: at each level, add the subtree
  contribution from ancestors that contain `s`.
  -/
    branchSupport (Combinatorial_Support T.Root)
        = branchSupport T.Childs := by rw [hroot_childs]
    _ = branchSupport (G.childrenFinset level cell) := by rw [hchilds_finset]
    _ = cell := branchSupport_childrenFinset_eq G level cell hcell

/-- Algebraic identity behind the refinement-tree linear combination: the indicator of the
left support `A` is a linear combination of the indicator of `A ∪ B` and the Haar wavelet
associated with the split `(A, B)`. -/
lemma indicator_left_eq_union_indicator_add_mul_haarWavelet

  /--
  Repackages the chain expansion into the subtree-sum form
  `sumDownSubTree_normed_indicator`.
  -/
    (μ : MeasureTheory.Measure α) (A B : Set α)
    (hAB : Disjoint A B)
    (hA_ne : (μ A).toReal ≠ 0)
    (hB_ne : (μ B).toReal ≠ 0)
    (hsum_ne : (μ A).toReal + (μ B).toReal ≠ 0) :
    (fun x => Set.indicator A (fun _ => (1 : ℝ)) x)
      =
    (fun x =>
      ((μ A).toReal / ((μ A).toReal + (μ B).toReal)) *
        Set.indicator (A ∪ B) (fun _ => (1 : ℝ)) x
      +
      (((μ A).toReal * (μ B).toReal) / ((μ A).toReal + (μ B).toReal)) *
        haarWavelet μ A B x) := by
  funext x
  have hAB' := Set.disjoint_left.mp hAB
  by_cases hxA : x ∈ A
  · have hxB : x ∉ B := by
      intro hxB
      exact (hAB' hxA hxB).elim
    simp [haarWavelet, hxA, hxB]
    field_simp [hA_ne, hsum_ne]
  · by_cases hxB : x ∈ B
    · simp [haarWavelet, hxA, hxB]
      field_simp [hB_ne, hsum_ne]
      ring
    · have hxUnion : x ∉ A ∪ B := by
        intro hx
        exact hx.elim hxA hxB
      simp [haarWavelet, hxA, hxB, hxUnion]

/-- Symmetric algebraic identity for the right support `B`: its indicator is a linear
combination of the indicator of `A ∪ B` and the Haar wavelet associated with `(A, B)`.
The Haar coefficient has a minus sign because `haarWavelet μ A B` is positive on `A`
and negative on `B`. -/
lemma indicator_right_eq_union_indicator_sub_mul_haarWavelet
    (μ : MeasureTheory.Measure α) (A B : Set α)
    (hAB : Disjoint A B)
    (hA_ne : (μ A).toReal ≠ 0)
    (hB_ne : (μ B).toReal ≠ 0)
    (hsum_ne : (μ A).toReal + (μ B).toReal ≠ 0) :
    (fun x => Set.indicator B (fun _ => (1 : ℝ)) x)
      =
    (fun x =>
      ((μ B).toReal / ((μ A).toReal + (μ B).toReal)) *
        Set.indicator (A ∪ B) (fun _ => (1 : ℝ)) x
      -
      (((μ A).toReal * (μ B).toReal) / ((μ A).toReal + (μ B).toReal)) *
        haarWavelet μ A B x) := by
  funext x
  have hAB' := Set.disjoint_left.mp hAB
  by_cases hxA : x ∈ A
  · have hxB : x ∉ B := by
      intro hxB
      exact (hAB' hxA hxB).elim
    simp [haarWavelet, hxA, hxB]
    field_simp [hA_ne, hsum_ne]
    ring
  · by_cases hxB : x ∈ B
    · simp [haarWavelet, hxA, hxB]
      field_simp [hB_ne, hsum_ne]
      ring
    · have hxUnion : x ∉ A ∪ B := by
        intro hx
        exact hx.elim hxA hxB
      simp [haarWavelet, hxA, hxB, hxUnion]

/-- Normalized version of the left refinement identity:
`1_A / μ(A)` is `1_{A ∪ B} / (μ(A)+μ(B))` plus an explicit multiple of the
Haar wavelet associated with `(A, B)`. -/
lemma normalized_indicator_left_eq_union_add_mul_haarWavelet
    (μ : MeasureTheory.Measure α) (A B : Set α)
    (hAB : Disjoint A B)
    (hA_ne : (μ A).toReal ≠ 0)
    (hB_ne : (μ B).toReal ≠ 0)
    (hsum_ne : (μ A).toReal + (μ B).toReal ≠ 0) :
    (fun x => Set.indicator A (fun _ => 1 / (μ A).toReal) x)
      =
    (fun x =>
      Set.indicator (A ∪ B)
        (fun _ => 1 / ((μ A).toReal + (μ B).toReal)) x
      +
      ((μ B).toReal / ((μ A).toReal + (μ B).toReal)) *
        haarWavelet μ A B x) := by
  funext x
  have hAB' := Set.disjoint_left.mp hAB
  by_cases hxA : x ∈ A
  · have hxB : x ∉ B := by
      intro hxB
      exact (hAB' hxA hxB).elim
    simp [haarWavelet, hxA, hxB]
    field_simp [hA_ne, hsum_ne]
  · by_cases hxB : x ∈ B
    · simp [haarWavelet, hxA, hxB]
      field_simp [hB_ne, hsum_ne]
      ring
    · have hxUnion : x ∉ A ∪ B := by
        intro hx
        exact hx.elim hxA hxB
      simp [haarWavelet, hxA, hxB, hxUnion]

/-- Normalized version of the right refinement identity.  The coefficient of the Haar wavelet
has a minus sign because `haarWavelet μ A B` is negative on `B`. -/
lemma normalized_indicator_right_eq_union_sub_mul_haarWavelet
    (μ : MeasureTheory.Measure α) (A B : Set α)
    (hAB : Disjoint A B)
    (hA_ne : (μ A).toReal ≠ 0)
    (hB_ne : (μ B).toReal ≠ 0)
    (hsum_ne : (μ A).toReal + (μ B).toReal ≠ 0) :
    (fun x => Set.indicator B (fun _ => 1 / (μ B).toReal) x)
      =
    (fun x =>
      Set.indicator (A ∪ B)
        (fun _ => 1 / ((μ A).toReal + (μ B).toReal)) x
      -
      ((μ A).toReal / ((μ A).toReal + (μ B).toReal)) *
        haarWavelet μ A B x) := by
  funext x
  have hAB' := Set.disjoint_left.mp hAB
  by_cases hxA : x ∈ A
  · have hxB : x ∉ B := by
      intro hxB
      exact (hAB' hxA hxB).elim
    simp [haarWavelet, hxA, hxB]
    field_simp [hA_ne, hsum_ne]
    ring
  · by_cases hxB : x ∈ B
    · simp [haarWavelet, hxA, hxB]
      field_simp [hB_ne, hsum_ne]
      ring
    · have hxUnion : x ∉ A ∪ B := by
        intro hx
        exact hx.elim hxA hxB
      simp [haarWavelet, hxA, hxB, hxUnion]

/-- For a branch `r = (A, B)` in the refinement tree, the characteristic function of the
support of `A` is the characteristic function of the support of `A ∪ B`, plus a scalar
multiple of the Haar wavelet associated with `(A, B)`. -/
lemma LinearCombinationRefinementTreeBasic
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level}
    {r : Finset (Set α) × Finset (Set α)}
    (hr : r ∈ (H.binaryRefinement.tree level cell hcell).Branches) :
    (fun x => Set.indicator (branchSupport r.1) (fun _ => (1 : ℝ)) x)
      =
    (fun x =>
      ((G.μ (branchSupport r.1)).toReal /
          ((G.μ (branchSupport r.1)).toReal + (G.μ (branchSupport r.2)).toReal)) *
        Set.indicator (branchSupport (r.1 ∪ r.2)) (fun _ => (1 : ℝ)) x
      +
      (((G.μ (branchSupport r.1)).toReal * (G.μ (branchSupport r.2)).toReal) /
          ((G.μ (branchSupport r.1)).toReal + (G.μ (branchSupport r.2)).toReal)) *
        haarWavelet G.μ (branchSupport r.1) (branchSupport r.2) x) := by
  let T := H.binaryRefinement.tree level cell hcell
  have hchilds : r.1 ⊆ T.Childs ∧ r.2 ⊆ T.Childs :=
    T.TreeStructureChilds r hr
  have hA_part : ∀ s, s ∈ r.1 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1 (hchilds.1 hs) |>.1
  have hB_part : ∀ s, s ∈ r.2 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1 (hchilds.2 hs) |>.1
  have hA_pos_cells : ∀ s, s ∈ r.1 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (level + 1) s (hA_part s hs)
  have hB_pos_cells : ∀ s, s ∈ r.2 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (level + 1) s (hB_part s hs)
  have hA_pos : 0 < G.μ (branchSupport r.1) :=
    measure_branchSupport_pos_of_nonempty G r.1 hA_pos_cells (T.NonemptyPairs r hr).1
  have hB_pos : 0 < G.μ (branchSupport r.2) :=
    measure_branchSupport_pos_of_nonempty G r.2 hB_pos_cells (T.NonemptyPairs r hr).2
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  have hA_lt_top : G.μ (branchSupport r.1) < ⊤ :=
    MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport r.1)
  have hB_lt_top : G.μ (branchSupport r.2) < ⊤ :=
    MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport r.2)
  have hA_toReal_pos : 0 < (G.μ (branchSupport r.1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hA_pos) hA_lt_top.ne
  have hB_toReal_pos : 0 < (G.μ (branchSupport r.2)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hB_pos) hB_lt_top.ne
  have hA_ne : (G.μ (branchSupport r.1)).toReal ≠ 0 := ne_of_gt hA_toReal_pos
  have hB_ne : (G.μ (branchSupport r.2)).toReal ≠ 0 := ne_of_gt hB_toReal_pos
  have hsum_ne :
      (G.μ (branchSupport r.1)).toReal + (G.μ (branchSupport r.2)).toReal ≠ 0 :=
    ne_of_gt (add_pos hA_toReal_pos hB_toReal_pos)
  have hAB : Disjoint (branchSupport r.1) (branchSupport r.2) :=
    disjoint_branchSupport_of_finset_disjoint G level r.1 r.2 hA_part hB_part
      (T.DisjointComponents r hr)
  have hsupport_union :
      branchSupport (r.1 ∪ r.2) = branchSupport r.1 ∪ branchSupport r.2 := by
    exact branchSupport_union r.1 r.2
  simpa [hsupport_union] using
    indicator_left_eq_union_indicator_add_mul_haarWavelet
      G.μ (branchSupport r.1) (branchSupport r.2) hAB hA_ne hB_ne hsum_ne

/-- The symmetric refinement-tree step for the right side of a branch. -/
lemma LinearCombinationRefinementTreeBasicRight
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level}
    {r : Finset (Set α) × Finset (Set α)}
    (hr : r ∈ (H.binaryRefinement.tree level cell hcell).Branches) :
    (fun x => Set.indicator (branchSupport r.2) (fun _ => (1 : ℝ)) x)
      =
    (fun x =>
      ((G.μ (branchSupport r.2)).toReal /
          ((G.μ (branchSupport r.1)).toReal + (G.μ (branchSupport r.2)).toReal)) *
        Set.indicator (branchSupport (r.1 ∪ r.2)) (fun _ => (1 : ℝ)) x
      -
      (((G.μ (branchSupport r.1)).toReal * (G.μ (branchSupport r.2)).toReal) /
          ((G.μ (branchSupport r.1)).toReal + (G.μ (branchSupport r.2)).toReal)) *
        haarWavelet G.μ (branchSupport r.1) (branchSupport r.2) x) := by
  let T := H.binaryRefinement.tree level cell hcell
  have hchilds : r.1 ⊆ T.Childs ∧ r.2 ⊆ T.Childs :=
    T.TreeStructureChilds r hr
  have hA_part : ∀ s, s ∈ r.1 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1 (hchilds.1 hs) |>.1
  have hB_part : ∀ s, s ∈ r.2 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1 (hchilds.2 hs) |>.1
  have hA_pos_cells : ∀ s, s ∈ r.1 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (level + 1) s (hA_part s hs)
  have hB_pos_cells : ∀ s, s ∈ r.2 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (level + 1) s (hB_part s hs)
  have hA_pos : 0 < G.μ (branchSupport r.1) :=
    measure_branchSupport_pos_of_nonempty G r.1 hA_pos_cells (T.NonemptyPairs r hr).1
  have hB_pos : 0 < G.μ (branchSupport r.2) :=
    measure_branchSupport_pos_of_nonempty G r.2 hB_pos_cells (T.NonemptyPairs r hr).2
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  have hA_lt_top : G.μ (branchSupport r.1) < ⊤ :=
    MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport r.1)
  have hB_lt_top : G.μ (branchSupport r.2) < ⊤ :=
    MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport r.2)
  have hA_toReal_pos : 0 < (G.μ (branchSupport r.1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hA_pos) hA_lt_top.ne
  have hB_toReal_pos : 0 < (G.μ (branchSupport r.2)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hB_pos) hB_lt_top.ne
  have hA_ne : (G.μ (branchSupport r.1)).toReal ≠ 0 := ne_of_gt hA_toReal_pos
  have hB_ne : (G.μ (branchSupport r.2)).toReal ≠ 0 := ne_of_gt hB_toReal_pos
  have hsum_ne :
      (G.μ (branchSupport r.1)).toReal + (G.μ (branchSupport r.2)).toReal ≠ 0 :=
    ne_of_gt (add_pos hA_toReal_pos hB_toReal_pos)
  have hAB : Disjoint (branchSupport r.1) (branchSupport r.2) :=
    disjoint_branchSupport_of_finset_disjoint G level r.1 r.2 hA_part hB_part
      (T.DisjointComponents r hr)
  have hsupport_union :
      branchSupport (r.1 ∪ r.2) = branchSupport r.1 ∪ branchSupport r.2 :=
    branchSupport_union r.1 r.2
  simpa [hsupport_union] using
    indicator_right_eq_union_indicator_sub_mul_haarWavelet
      G.μ (branchSupport r.1) (branchSupport r.2) hAB hA_ne hB_ne hsum_ne

/-- Normalized left one-step identity for a refinement-tree branch. -/
lemma NormalizedLinearCombinationRefinementTreeBasic
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level}
    {r : Finset (Set α) × Finset (Set α)}
    (hr : r ∈ (H.binaryRefinement.tree level cell hcell).Branches) :
    (fun x =>
      Set.indicator (branchSupport r.1)
        (fun _ => 1 / (G.μ (branchSupport r.1)).toReal) x)
      =
    (fun x =>
      Set.indicator (branchSupport (r.1 ∪ r.2))
        (fun _ =>
          1 / ((G.μ (branchSupport r.1)).toReal +
            (G.μ (branchSupport r.2)).toReal)) x
      +
      ((G.μ (branchSupport r.2)).toReal /
          ((G.μ (branchSupport r.1)).toReal +
            (G.μ (branchSupport r.2)).toReal)) *
        haarWavelet G.μ (branchSupport r.1) (branchSupport r.2) x) := by
  let T := H.binaryRefinement.tree level cell hcell
  have hchilds : r.1 ⊆ T.Childs ∧ r.2 ⊆ T.Childs :=
    T.TreeStructureChilds r hr
  have hA_part : ∀ s, s ∈ r.1 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1 (hchilds.1 hs) |>.1
  have hB_part : ∀ s, s ∈ r.2 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1 (hchilds.2 hs) |>.1
  have hA_pos_cells : ∀ s, s ∈ r.1 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (level + 1) s (hA_part s hs)
  have hB_pos_cells : ∀ s, s ∈ r.2 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (level + 1) s (hB_part s hs)
  have hA_pos : 0 < G.μ (branchSupport r.1) :=
    measure_branchSupport_pos_of_nonempty G r.1 hA_pos_cells (T.NonemptyPairs r hr).1
  have hB_pos : 0 < G.μ (branchSupport r.2) :=
    measure_branchSupport_pos_of_nonempty G r.2 hB_pos_cells (T.NonemptyPairs r hr).2
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  have hA_lt_top : G.μ (branchSupport r.1) < ⊤ :=
    MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport r.1)
  have hB_lt_top : G.μ (branchSupport r.2) < ⊤ :=
    MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport r.2)
  have hA_toReal_pos : 0 < (G.μ (branchSupport r.1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hA_pos) hA_lt_top.ne
  have hB_toReal_pos : 0 < (G.μ (branchSupport r.2)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hB_pos) hB_lt_top.ne
  have hA_ne : (G.μ (branchSupport r.1)).toReal ≠ 0 := ne_of_gt hA_toReal_pos
  have hB_ne : (G.μ (branchSupport r.2)).toReal ≠ 0 := ne_of_gt hB_toReal_pos
  have hsum_ne :
      (G.μ (branchSupport r.1)).toReal + (G.μ (branchSupport r.2)).toReal ≠ 0 :=
    ne_of_gt (add_pos hA_toReal_pos hB_toReal_pos)
  have hAB : Disjoint (branchSupport r.1) (branchSupport r.2) :=
    disjoint_branchSupport_of_finset_disjoint G level r.1 r.2 hA_part hB_part
      (T.DisjointComponents r hr)
  have hsupport_union :
      branchSupport (r.1 ∪ r.2) = branchSupport r.1 ∪ branchSupport r.2 :=
    branchSupport_union r.1 r.2
  simpa [hsupport_union] using
    normalized_indicator_left_eq_union_add_mul_haarWavelet
      G.μ (branchSupport r.1) (branchSupport r.2) hAB hA_ne hB_ne hsum_ne

/-- Normalized right one-step identity for a refinement-tree branch. -/
lemma NormalizedLinearCombinationRefinementTreeBasicRight
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level}
    {r : Finset (Set α) × Finset (Set α)}
    (hr : r ∈ (H.binaryRefinement.tree level cell hcell).Branches) :
    (fun x =>
      Set.indicator (branchSupport r.2)
        (fun _ => 1 / (G.μ (branchSupport r.2)).toReal) x)
      =
    (fun x =>
      Set.indicator (branchSupport (r.1 ∪ r.2))
        (fun _ =>
          1 / ((G.μ (branchSupport r.1)).toReal +
            (G.μ (branchSupport r.2)).toReal)) x
      -
      ((G.μ (branchSupport r.1)).toReal /
          ((G.μ (branchSupport r.1)).toReal +
            (G.μ (branchSupport r.2)).toReal)) *
        haarWavelet G.μ (branchSupport r.1) (branchSupport r.2) x) := by
  let T := H.binaryRefinement.tree level cell hcell
  have hchilds : r.1 ⊆ T.Childs ∧ r.2 ⊆ T.Childs :=
    T.TreeStructureChilds r hr
  have hA_part : ∀ s, s ∈ r.1 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1 (hchilds.1 hs) |>.1
  have hB_part : ∀ s, s ∈ r.2 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1 (hchilds.2 hs) |>.1
  have hA_pos_cells : ∀ s, s ∈ r.1 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (level + 1) s (hA_part s hs)
  have hB_pos_cells : ∀ s, s ∈ r.2 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (level + 1) s (hB_part s hs)
  have hA_pos : 0 < G.μ (branchSupport r.1) :=
    measure_branchSupport_pos_of_nonempty G r.1 hA_pos_cells (T.NonemptyPairs r hr).1
  have hB_pos : 0 < G.μ (branchSupport r.2) :=
    measure_branchSupport_pos_of_nonempty G r.2 hB_pos_cells (T.NonemptyPairs r hr).2
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  have hA_lt_top : G.μ (branchSupport r.1) < ⊤ :=
    MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport r.1)
  have hB_lt_top : G.μ (branchSupport r.2) < ⊤ :=
    MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport r.2)
  have hA_toReal_pos : 0 < (G.μ (branchSupport r.1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hA_pos) hA_lt_top.ne
  have hB_toReal_pos : 0 < (G.μ (branchSupport r.2)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hB_pos) hB_lt_top.ne
  have hA_ne : (G.μ (branchSupport r.1)).toReal ≠ 0 := ne_of_gt hA_toReal_pos
  have hB_ne : (G.μ (branchSupport r.2)).toReal ≠ 0 := ne_of_gt hB_toReal_pos
  have hsum_ne :
      (G.μ (branchSupport r.1)).toReal + (G.μ (branchSupport r.2)).toReal ≠ 0 :=
    ne_of_gt (add_pos hA_toReal_pos hB_toReal_pos)
  have hAB : Disjoint (branchSupport r.1) (branchSupport r.2) :=
    disjoint_branchSupport_of_finset_disjoint G level r.1 r.2 hA_part hB_part
      (T.DisjointComponents r hr)
  have hsupport_union :
      branchSupport (r.1 ∪ r.2) = branchSupport r.1 ∪ branchSupport r.2 :=
    branchSupport_union r.1 r.2
  simpa [hsupport_union] using
    normalized_indicator_right_eq_union_sub_mul_haarWavelet
      G.μ (branchSupport r.1) (branchSupport r.2) hAB hA_ne hB_ne hsum_ne

/-- For a refinement-tree branch, the real measure of the union support is the sum of the
real measures of the two side supports. -/
lemma branchSupport_union_measure_toReal_eq_add
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level}
    {r : Finset (Set α) × Finset (Set α)}
    (hr : r ∈ (H.binaryRefinement.tree level cell hcell).Branches) :
    (G.μ (branchSupport (r.1 ∪ r.2))).toReal
      =
    (G.μ (branchSupport r.1)).toReal + (G.μ (branchSupport r.2)).toReal := by
  let T := H.binaryRefinement.tree level cell hcell
  have hchilds : r.1 ⊆ T.Childs ∧ r.2 ⊆ T.Childs :=
    T.TreeStructureChilds r hr
  have hA_part : ∀ s, s ∈ r.1 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1 (hchilds.1 hs) |>.1
  have hB_part : ∀ s, s ∈ r.2 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1 (hchilds.2 hs) |>.1
  have hAB : Disjoint (branchSupport r.1) (branchSupport r.2) :=
    disjoint_branchSupport_of_finset_disjoint G level r.1 r.2 hA_part hB_part
      (T.DisjointComponents r hr)
  have hB_meas : MeasurableSet (branchSupport r.2) :=
    measurableSet_branchSupport_of_partition G level r.2 hB_part
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  have hA_ne_top : G.μ (branchSupport r.1) ≠ ⊤ :=
    (MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport r.1)).ne
  have hB_ne_top : G.μ (branchSupport r.2) ≠ ⊤ :=
    (MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport r.2)).ne
  calc
    (G.μ (branchSupport (r.1 ∪ r.2))).toReal
        = (G.μ (branchSupport r.1 ∪ branchSupport r.2)).toReal := by
            rw [branchSupport_union]
    _ = (G.μ (branchSupport r.1) + G.μ (branchSupport r.2)).toReal := by
            rw [MeasureTheory.measure_union hAB hB_meas]
    _ = (G.μ (branchSupport r.1)).toReal + (G.μ (branchSupport r.2)).toReal := by
            exact ENNReal.toReal_add hA_ne_top hB_ne_top

/-- Normalized left one-step identity with the parent denominator written as the measure of the
parent support. -/
lemma NormalizedLinearCombinationRefinementTreeBasic_parent
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level}
    {r : Finset (Set α) × Finset (Set α)}
    (hr : r ∈ (H.binaryRefinement.tree level cell hcell).Branches) :
    (fun x =>
      Set.indicator (branchSupport r.1)
        (fun _ => 1 / (G.μ (branchSupport r.1)).toReal) x)
      =
    (fun x =>
      Set.indicator (branchSupport (r.1 ∪ r.2))
        (fun _ => 1 / (G.μ (branchSupport (r.1 ∪ r.2))).toReal) x
      +
      ((G.μ (branchSupport r.2)).toReal /
          (G.μ (branchSupport (r.1 ∪ r.2))).toReal) *
        haarWavelet G.μ (branchSupport r.1) (branchSupport r.2) x) := by
  have hbasic := NormalizedLinearCombinationRefinementTreeBasic
    (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell) hr
  have hμ := branchSupport_union_measure_toReal_eq_add
    (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell) hr
  simpa [hμ] using hbasic

/-- Normalized right one-step identity with the parent denominator written as the measure of the
parent support. -/
lemma NormalizedLinearCombinationRefinementTreeBasicRight_parent
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level}
    {r : Finset (Set α) × Finset (Set α)}
    (hr : r ∈ (H.binaryRefinement.tree level cell hcell).Branches) :
    (fun x =>
      Set.indicator (branchSupport r.2)
        (fun _ => 1 / (G.μ (branchSupport r.2)).toReal) x)
      =
    (fun x =>
      Set.indicator (branchSupport (r.1 ∪ r.2))
        (fun _ => 1 / (G.μ (branchSupport (r.1 ∪ r.2))).toReal) x
      -
      ((G.μ (branchSupport r.1)).toReal /
          (G.μ (branchSupport (r.1 ∪ r.2))).toReal) *
        haarWavelet G.μ (branchSupport r.1) (branchSupport r.2) x) := by
  have hbasic := NormalizedLinearCombinationRefinementTreeBasicRight
    (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell) hr
  have hμ := branchSupport_union_measure_toReal_eq_add
    (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell) hr
  simpa [hμ] using hbasic

/-- Explicit normalized expansion along the chain from the root of the binary refinement tree
to the top `{s}`.  The sum over `i < n` records the ancestors of the final branch, and the
last displayed term is the contribution of the final branch whose left or right side is `{s}`. -/
theorem normalized_indicator_child_eq_cell_add_sum_chain
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell s : Set α} (hcell : cell ∈ G.grid.partitions level)
    (hs_child : s ∈ G.children level cell) :
    ∃ n : ℕ, ∃ chain : ℕ → (Finset (Set α) × Finset (Set α)),
      chain 0 = (H.binaryRefinement.tree level cell hcell).Root ∧
      (({s} : Finset (Set α)) = (chain n).1 ∨ ({s} : Finset (Set α)) = (chain n).2) ∧
      (∀ i ≤ n, chain i ∈ (H.binaryRefinement.tree level cell hcell).Branches) ∧
      (∀ i < n,
        Combinatorial_Support (chain (i + 1)) = (chain i).1 ∨
        Combinatorial_Support (chain (i + 1)) = (chain i).2) ∧
      (fun x => Set.indicator s (fun _ => 1 / (G.μ s).toReal) x)
        =
      (fun x =>
        Set.indicator cell (fun _ => 1 / (G.μ cell).toReal) x
        +
        ∑ i ∈ Finset.range n,
          (if Combinatorial_Support (chain (i + 1)) = (chain i).1 then
              (G.μ (branchSupport (chain i).2)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal
            else
              -((G.μ (branchSupport (chain i).1)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal))
            * haarWavelet G.μ (branchSupport (chain i).1) (branchSupport (chain i).2) x
        +
        (if ({s} : Finset (Set α)) = (chain n).1 then
            (G.μ (branchSupport (chain n).2)).toReal /
              (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal
          else
            -((G.μ (branchSupport (chain n).1)).toReal /
              (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal))
          * haarWavelet G.μ (branchSupport (chain n).1) (branchSupport (chain n).2) x) := by
  classical
  let T := H.binaryRefinement.tree level cell hcell
  have hs_top : s ∈ T.Tops :=
    (H.binaryRefinement.tops_are_children level cell hcell s).2 hs_child
  rcases exists_chain_from_root_to_top (T := T) hs_top with
    ⟨n, chain, hchain_zero, hchain_top, hchain_mem, hchain_step⟩
  refine ⟨n, chain, hchain_zero, hchain_top, hchain_mem, hchain_step, ?_⟩
  let coeff : ℕ → ℝ := fun i =>
    if Combinatorial_Support (chain (i + 1)) = (chain i).1 then
      (G.μ (branchSupport (chain i).2)).toReal /
        (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal
    else
      -((G.μ (branchSupport (chain i).1)).toReal /
        (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal)
  have hancestor :
      ∀ k, k ≤ n →
        (fun x =>
          Set.indicator (branchSupport (Combinatorial_Support (chain k)))
            (fun _ =>
              1 / (G.μ (branchSupport (Combinatorial_Support (chain k)))).toReal) x)
          =
        (fun x =>
          Set.indicator cell (fun _ => 1 / (G.μ cell).toReal) x
          +
          ∑ i ∈ Finset.range k,
            coeff i *
              haarWavelet G.μ (branchSupport (chain i).1) (branchSupport (chain i).2) x) := by
    intro k hk
    induction k with
    | zero =>
        funext x
        have hroot :
            branchSupport (Combinatorial_Support (chain 0)) = cell := by
          rw [hchain_zero]
          exact branchSupport_root_eq_cell G H
        simp [hroot]
    | succ i ih =>
        have hi_le : i ≤ n := by omega
        have hi_lt : i < n := by omega
        have hbranch_i : chain i ∈ T.Branches := hchain_mem i hi_le
        have hparent_union :
            branchSupport ((chain i).1 ∪ (chain i).2)
              = branchSupport (Combinatorial_Support (chain i)) := by
          rfl
        rcases hchain_step i hi_lt with hleft | hright
        · funext x
          have hbasic := congrFun
            (NormalizedLinearCombinationRefinementTreeBasic_parent
              (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell)
              (r := chain i) hbranch_i) x
          have hside :
              branchSupport (Combinatorial_Support (chain (i + 1)))
                = branchSupport (chain i).1 := by
            rw [hleft]
          have hparent := congrFun (ih hi_le) x
          calc
            Set.indicator (branchSupport (Combinatorial_Support (chain (i + 1))))
                (fun _ =>
                  1 / (G.μ (branchSupport (Combinatorial_Support (chain (i + 1))))).toReal) x
                =
              Set.indicator (branchSupport (chain i).1)
                (fun _ => 1 / (G.μ (branchSupport (chain i).1)).toReal) x := by
                simp [hside]
            _ =
              Set.indicator (branchSupport ((chain i).1 ∪ (chain i).2))
                (fun _ => 1 / (G.μ (branchSupport ((chain i).1 ∪ (chain i).2))).toReal) x
              +
              ((G.μ (branchSupport (chain i).2)).toReal /
                  (G.μ (branchSupport ((chain i).1 ∪ (chain i).2))).toReal) *
                haarWavelet G.μ (branchSupport (chain i).1) (branchSupport (chain i).2) x := by
                simpa using hbasic
            _ =
              Set.indicator cell (fun _ => 1 / (G.μ cell).toReal) x
              +
              ∑ j ∈ Finset.range (i + 1),
                coeff j *
                  haarWavelet G.μ (branchSupport (chain j).1) (branchSupport (chain j).2) x := by
                rw [hparent_union]
                rw [hparent]
                simp [Finset.sum_range_succ, coeff, hleft]
                ring_nf
        · funext x
          have hbasic := congrFun
            (NormalizedLinearCombinationRefinementTreeBasicRight_parent
              (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell)
              (r := chain i) hbranch_i) x
          have hright_ne_left : (chain i).2 ≠ (chain i).1 := by
            intro h
            have hdisj := T.DisjointComponents (chain i) hbranch_i
            obtain ⟨y, hy⟩ := (T.NonemptyPairs (chain i) hbranch_i).2
            have hy_left : y ∈ (chain i).1 := by
              simpa [h] using hy
            exact Finset.disjoint_left.mp hdisj hy_left hy
          have hnot_left :
              ¬ Combinatorial_Support (chain (i + 1)) = (chain i).1 := by
            intro h
            exact hright_ne_left (by rw [← hright, h])
          have hside :
              branchSupport (Combinatorial_Support (chain (i + 1)))
                = branchSupport (chain i).2 := by
            rw [hright]
          have hparent := congrFun (ih hi_le) x
          calc
            Set.indicator (branchSupport (Combinatorial_Support (chain (i + 1))))
                (fun _ =>
                  1 / (G.μ (branchSupport (Combinatorial_Support (chain (i + 1))))).toReal) x
                =
              Set.indicator (branchSupport (chain i).2)
                (fun _ => 1 / (G.μ (branchSupport (chain i).2)).toReal) x := by
                simp [hside]
            _ =
              Set.indicator (branchSupport ((chain i).1 ∪ (chain i).2))
                (fun _ => 1 / (G.μ (branchSupport ((chain i).1 ∪ (chain i).2))).toReal) x
              -
              ((G.μ (branchSupport (chain i).1)).toReal /
                  (G.μ (branchSupport ((chain i).1 ∪ (chain i).2))).toReal) *
                haarWavelet G.μ (branchSupport (chain i).1) (branchSupport (chain i).2) x := by
                simpa using hbasic
            _ =
              Set.indicator cell (fun _ => 1 / (G.μ cell).toReal) x
              +
              ∑ j ∈ Finset.range (i + 1),
                coeff j *
                  haarWavelet G.μ (branchSupport (chain j).1) (branchSupport (chain j).2) x := by
                rw [hparent_union]
                rw [hparent]
                simp [Finset.sum_range_succ, coeff, hnot_left]
                ring_nf
  funext x
  have hbranch_n : chain n ∈ T.Branches := hchain_mem n le_rfl
  have hparent_n := congrFun (hancestor n le_rfl) x
  have hparent_union :
      branchSupport ((chain n).1 ∪ (chain n).2)
        = branchSupport (Combinatorial_Support (chain n)) := by
    rfl
  rcases hchain_top with htop_left | htop_right
  · have hbasic := congrFun
      (NormalizedLinearCombinationRefinementTreeBasic_parent
        (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell)
        (r := chain n) hbranch_n) x
    have hsingle : branchSupport (chain n).1 = s := by
      rw [← htop_left]
      exact branchSupport_singleton s
    calc
      Set.indicator s (fun _ => 1 / (G.μ s).toReal) x
          =
        Set.indicator (branchSupport (chain n).1)
          (fun _ => 1 / (G.μ (branchSupport (chain n).1)).toReal) x := by
          simp [hsingle]
      _ =
        Set.indicator (branchSupport ((chain n).1 ∪ (chain n).2))
          (fun _ => 1 / (G.μ (branchSupport ((chain n).1 ∪ (chain n).2))).toReal) x
        +
        ((G.μ (branchSupport (chain n).2)).toReal /
            (G.μ (branchSupport ((chain n).1 ∪ (chain n).2))).toReal) *
          haarWavelet G.μ (branchSupport (chain n).1) (branchSupport (chain n).2) x := by
          simpa using hbasic
      _ =
        Set.indicator cell (fun _ => 1 / (G.μ cell).toReal) x
        +
        ∑ i ∈ Finset.range n,
          (if Combinatorial_Support (chain (i + 1)) = (chain i).1 then
              (G.μ (branchSupport (chain i).2)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal
            else
              -((G.μ (branchSupport (chain i).1)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal))
            * haarWavelet G.μ (branchSupport (chain i).1) (branchSupport (chain i).2) x
        +
        (if ({s} : Finset (Set α)) = (chain n).1 then
            (G.μ (branchSupport (chain n).2)).toReal /
              (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal
          else
            -((G.μ (branchSupport (chain n).1)).toReal /
              (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal))
          * haarWavelet G.μ (branchSupport (chain n).1) (branchSupport (chain n).2) x := by
          rw [hparent_union]
          rw [hparent_n]
          simp [coeff, htop_left]
  · have hbasic := congrFun
      (NormalizedLinearCombinationRefinementTreeBasicRight_parent
        (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell)
        (r := chain n) hbranch_n) x
    have hright_ne_left : (chain n).2 ≠ (chain n).1 := by
      intro h
      have hdisj := T.DisjointComponents (chain n) hbranch_n
      obtain ⟨y, hy⟩ := (T.NonemptyPairs (chain n) hbranch_n).2
      have hy_left : y ∈ (chain n).1 := by
        simpa [h] using hy
      exact Finset.disjoint_left.mp hdisj hy_left hy
    have hnot_top_left : ¬ ({s} : Finset (Set α)) = (chain n).1 := by
      intro h
      exact hright_ne_left (by rw [← htop_right, h])
    have hsingle : branchSupport (chain n).2 = s := by
      rw [← htop_right]
      exact branchSupport_singleton s
    calc
      Set.indicator s (fun _ => 1 / (G.μ s).toReal) x
          =
        Set.indicator (branchSupport (chain n).2)
          (fun _ => 1 / (G.μ (branchSupport (chain n).2)).toReal) x := by
          simp [hsingle]
      _ =
        Set.indicator (branchSupport ((chain n).1 ∪ (chain n).2))
          (fun _ => 1 / (G.μ (branchSupport ((chain n).1 ∪ (chain n).2))).toReal) x
        -
        ((G.μ (branchSupport (chain n).1)).toReal /
            (G.μ (branchSupport ((chain n).1 ∪ (chain n).2))).toReal) *
          haarWavelet G.μ (branchSupport (chain n).1) (branchSupport (chain n).2) x := by
          simpa using hbasic
      _ =
        Set.indicator cell (fun _ => 1 / (G.μ cell).toReal) x
        +
        ∑ i ∈ Finset.range n,
          (if Combinatorial_Support (chain (i + 1)) = (chain i).1 then
              (G.μ (branchSupport (chain i).2)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal
            else
              -((G.μ (branchSupport (chain i).1)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal))
            * haarWavelet G.μ (branchSupport (chain i).1) (branchSupport (chain i).2) x
        +
        (if ({s} : Finset (Set α)) = (chain n).1 then
            (G.μ (branchSupport (chain n).2)).toReal /
              (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal
          else
            -((G.μ (branchSupport (chain n).1)).toReal /
              (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal))
          * haarWavelet G.μ (branchSupport (chain n).1) (branchSupport (chain n).2) x := by
          rw [hparent_union]
          rw [hparent_n]
          simp [coeff, hnot_top_left]
          ring_nf

/-- The branch-sum expansion of the normalized child indicator minus the normalized parent
indicator, indexed by all refinement-tree branches whose support contains `s`. -/
noncomputable def sumDownSubTree_normed_indicator
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} (hcell : cell ∈ G.grid.partitions level)
    (s : Set α) : α → ℝ :=
  fun x =>
    ∑ B ∈
      ((H.binaryRefinement.tree level cell hcell).Branches).filter
        (fun B => s ⊆ branchSupport (Combinatorial_Support B)),
      (if s ⊆ branchSupport B.1 then
          (G.μ (branchSupport B.2)).toReal /
            (G.μ (branchSupport (Combinatorial_Support B))).toReal
        else
          -((G.μ (branchSupport B.1)).toReal /
            (G.μ (branchSupport (Combinatorial_Support B))).toReal))
        * haarWavelet G.μ (branchSupport B.1) (branchSupport B.2) x


/--
Global ancestor-level sum for the normalized indicator expansion.

At each level below `level`, this adds the subtree contribution from partition
cells that contain `s`.
-/
noncomputable def sumDown_normed_indicator
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (s : Set α) (level : ℕ) (_hs : s ∈ G.grid.partitions level) : α → ℝ :=
  fun x =>
    ∑ i ∈ Finset.range level,
      ∑ c ∈ (G.grid.partitions i).attach.filter (fun c => s ⊆ c.1),
        sumDownSubTree_normed_indicator G H c.2 s x



/--
Repackages the chain-based expansion as a subtree-sum formula.
-/
theorem normalized_indicator_child_eq_cell_add_sum_chain_2
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell s : Set α} (hcell : cell ∈ G.grid.partitions level)
    (hs_child : s ∈ G.children level cell) :
    (fun x =>
      Set.indicator s (fun _ => 1 / (G.μ s).toReal) x
      -
      Set.indicator cell (fun _ => 1 / (G.μ cell).toReal) x)
      =
    sumDownSubTree_normed_indicator G H hcell s := by
  classical
  let T := H.binaryRefinement.tree level cell hcell
  let F : Finset (Finset (Set α) × Finset (Set α)) :=
    T.Branches.filter (fun B => s ⊆ branchSupport (Combinatorial_Support B))
  let term : (Finset (Set α) × Finset (Set α)) → α → ℝ := fun B x =>
    (if s ⊆ branchSupport B.1 then
        (G.μ (branchSupport B.2)).toReal /
          (G.μ (branchSupport (Combinatorial_Support B))).toReal
      else
        -((G.μ (branchSupport B.1)).toReal /
          (G.μ (branchSupport (Combinatorial_Support B))).toReal))
      * haarWavelet G.μ (branchSupport B.1) (branchSupport B.2) x
  rcases normalized_indicator_child_eq_cell_add_sum_chain
      (G := G) (H := H) hcell hs_child with
    ⟨n, chain, hchain_zero, hchain_top, hchain_mem, hchain_step, hchain_sum⟩
  have hsupport_mem_iff :
      ∀ B, B ∈ T.Branches →
        (s ⊆ branchSupport (Combinatorial_Support B) ↔
          s ∈ Combinatorial_Support B) := by
    intro B hB
    have hB_childs : ∀ t, t ∈ Combinatorial_Support B → t ∈ G.children level cell := by
      intro t ht
      have hchilds := T.TreeStructureChilds B hB
      rcases Finset.mem_union.mp (by simpa [Combinatorial_Support] using ht) with ht1 | ht2
      · exact (H.binaryRefinement.childs_are_children level cell hcell t).1 (hchilds.1 ht1)
      · exact (H.binaryRefinement.childs_are_children level cell hcell t).1 (hchilds.2 ht2)
    exact child_subset_branchSupport_iff_mem G hs_child hB_childs
  have hsingleton_subset_chain :
      ∀ i, i ≤ n → ({s} : Finset (Set α)) ⊆ Combinatorial_Support (chain i) := by
    intro i hi
    have hend_subset :
        Combinatorial_Support (chain n) ⊆ Combinatorial_Support (chain i) :=
      chain_endpoint_support_subset (T := T) (p := chain n) (n := n) (c := chain)
        rfl hchain_step i hi
    have htop_subset_end :
        ({s} : Finset (Set α)) ⊆ Combinatorial_Support (chain n) := by
      rcases hchain_top with hleft | hright
      · intro t ht
        have ht_left : t ∈ (chain n).1 := by simpa [hleft] using ht
        dsimp [Combinatorial_Support]
        exact Finset.mem_union_left (chain n).2 ht_left
      · intro t ht
        have ht_right : t ∈ (chain n).2 := by simpa [hright] using ht
        dsimp [Combinatorial_Support]
        exact Finset.mem_union_right (chain n).1 ht_right
    exact htop_subset_end.trans hend_subset
  have hmem_filter_iff :
      ∀ B, B ∈ F ↔ ∃ i ∈ Finset.range (n + 1), chain i = B := by
    intro B
    constructor
    · intro hBF
      have hB : B ∈ T.Branches := by
        simpa [F] using (Finset.mem_filter.mp hBF).1
      have hs_subset : s ⊆ branchSupport (Combinatorial_Support B) := by
        simpa [F] using (Finset.mem_filter.mp hBF).2
      have hs_mem_B : s ∈ Combinatorial_Support B :=
        (hsupport_mem_iff B hB).1 hs_subset
      have hs_mem_end : s ∈ Combinatorial_Support (chain n) := by
        exact hsingleton_subset_chain n le_rfl (by simp)
      by_cases hBn : B = chain n
      · exact ⟨n, by simp, by simp [hBn]⟩
      have hsupport_cases := T.SupportProperty (chain n) (hchain_mem n le_rfl) B hB
        (by intro h; exact hBn h.symm)
      rcases hsupport_cases with hdisj | hsub_left | hsub_right | hBsub_left | hBsub_right
      · exact False.elim ((Finset.disjoint_left.mp hdisj) hs_mem_end hs_mem_B)
      · have hsub :
            Combinatorial_Support (chain n) ⊆ Combinatorial_Support B := by
          exact hsub_left.trans Finset.subset_union_left
        rcases (chain_from_root_exactly_support_containers
            (T := T) (p := chain n) (q := B)
            (hchain_mem n le_rfl) hB hchain_zero rfl hchain_mem hchain_step).2 hsub with
          ⟨i, hi, hiB⟩
        exact ⟨i, by simpa using hi, hiB⟩
      · have hsub :
            Combinatorial_Support (chain n) ⊆ Combinatorial_Support B := by
          exact hsub_right.trans Finset.subset_union_right
        rcases (chain_from_root_exactly_support_containers
            (T := T) (p := chain n) (q := B)
            (hchain_mem n le_rfl) hB hchain_zero rfl hchain_mem hchain_step).2 hsub with
          ⟨i, hi, hiB⟩
        exact ⟨i, by simpa using hi, hiB⟩
      · rcases hchain_top with htop_left | htop_right
        · have hB_singleton :
              Combinatorial_Support B ⊆ ({s} : Finset (Set α)) := by
            simpa [htop_left] using hBsub_left
          exact (branch_combinatorialSupport_not_subset_singleton
            (T := T) (B := B) hB s hB_singleton).elim
        · have hs_in_right : s ∈ (chain n).2 := by simp [← htop_right]
          have hs_in_left : s ∈ (chain n).1 := hBsub_left hs_mem_B
          exact (Finset.disjoint_left.mp
            (T.DisjointComponents (chain n) (hchain_mem n le_rfl)) hs_in_left hs_in_right).elim
      · rcases hchain_top with htop_left | htop_right
        · have hs_in_left : s ∈ (chain n).1 := by simp [← htop_left]
          have hs_in_right : s ∈ (chain n).2 := hBsub_right hs_mem_B
          exact (Finset.disjoint_left.mp
            (T.DisjointComponents (chain n) (hchain_mem n le_rfl)) hs_in_left hs_in_right).elim
        · have hB_singleton :
              Combinatorial_Support B ⊆ ({s} : Finset (Set α)) := by
            simpa [htop_right] using hBsub_right
          exact (branch_combinatorialSupport_not_subset_singleton
            (T := T) (B := B) hB s hB_singleton).elim
    · rintro ⟨i, hi_range, rfl⟩
      have hi : i ≤ n := by simpa [Finset.mem_range] using hi_range
      have hbranch_i : chain i ∈ T.Branches := hchain_mem i hi
      have hs_mem : s ∈ Combinatorial_Support (chain i) :=
        hsingleton_subset_chain i hi (by simp)
      have hs_subset :
          s ⊆ branchSupport (Combinatorial_Support (chain i)) :=
        (hsupport_mem_iff (chain i) hbranch_i).2 hs_mem
      exact by
        simp [F, hbranch_i, hs_subset]
  have hchain_inj :
      ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
        chain i = chain j → i = j := by
    intro i hi j hj hij
    have hi_le : i ≤ n := by simpa [Finset.mem_range] using hi
    have hj_le : j ≤ n := by simpa [Finset.mem_range] using hj
    have huniq := chain_from_root_unique
      (T := T) (p := chain i) (n1 := i) (n2 := j) (c1 := chain) (c2 := chain)
      (hchain_mem i hi_le)
      hchain_zero rfl
      (fun k hk => hchain_mem k (by omega))
      (fun k hk => hchain_step k (by omega))
      hchain_zero (by simp [hij])
      (fun k hk => hchain_mem k (by omega))
      (fun k hk => hchain_step k (by omega))
    exact huniq.1
  have hsum_bij :
      (fun x => ∑ i ∈ Finset.range (n + 1), term (chain i) x)
        =
      (fun x => ∑ B ∈ F, term B x) := by
    funext x
    refine Finset.sum_bij (fun i _ => chain i) ?_ ?_ ?_ ?_
    · intro i hi
      exact (hmem_filter_iff (chain i)).2 ⟨i, hi, rfl⟩
    · intro i hi j hj hij
      exact hchain_inj i hi j hj hij
    · intro B hBF
      rcases (hmem_filter_iff B).1 hBF with ⟨i, hi, hiB⟩
      exact ⟨i, hi, hiB⟩
    · intro i hi
      rfl
  have hcoeff_step :
      ∀ i, i < n →
        term (chain i) =
          (fun x =>
            (if Combinatorial_Support (chain (i + 1)) = (chain i).1 then
                (G.μ (branchSupport (chain i).2)).toReal /
                  (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal
              else
                -((G.μ (branchSupport (chain i).1)).toReal /
                  (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal))
              * haarWavelet G.μ (branchSupport (chain i).1) (branchSupport (chain i).2) x) := by
    intro i hi
    funext x
    have hi_le : i ≤ n := by omega
    have hbranch_i : chain i ∈ T.Branches := hchain_mem i hi_le
    have hleft_iff :
        s ⊆ branchSupport (chain i).1 ↔
          Combinatorial_Support (chain (i + 1)) = (chain i).1 := by
      constructor
      · intro hs_left
        rcases hchain_step i hi with hleft | hright
        · exact hleft
        · have hleft_childs : ∀ t, t ∈ (chain i).1 → t ∈ G.children level cell := by
            intro t ht
            exact (H.binaryRefinement.childs_are_children level cell hcell t).1
              ((T.TreeStructureChilds (chain i) hbranch_i).1 ht)
          have hs_mem_left : s ∈ (chain i).1 :=
            (child_subset_branchSupport_iff_mem G hs_child hleft_childs).1 hs_left
          have hs_mem_child : s ∈ Combinatorial_Support (chain (i + 1)) :=
            hsingleton_subset_chain (i + 1) (by omega) (by simp)
          have hs_mem_right : s ∈ (chain i).2 := by simpa [hright] using hs_mem_child
          exact (Finset.disjoint_left.mp
            (T.DisjointComponents (chain i) hbranch_i) hs_mem_left hs_mem_right).elim
      · intro hleft
        have hs_mem_child : s ∈ Combinatorial_Support (chain (i + 1)) :=
          hsingleton_subset_chain (i + 1) (by omega) (by simp)
        have hs_mem_left : s ∈ (chain i).1 := by simpa [hleft] using hs_mem_child
        exact subset_branchSupport_of_mem hs_mem_left
    simp [term, hleft_iff]
  have hcoeff_last :
      term (chain n) =
        (fun x =>
          (if ({s} : Finset (Set α)) = (chain n).1 then
              (G.μ (branchSupport (chain n).2)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal
            else
              -((G.μ (branchSupport (chain n).1)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal))
            * haarWavelet G.μ (branchSupport (chain n).1) (branchSupport (chain n).2) x) := by
    funext x
    have hbranch_n : chain n ∈ T.Branches := hchain_mem n le_rfl
    have hleft_iff :
        s ⊆ branchSupport (chain n).1 ↔ ({s} : Finset (Set α)) = (chain n).1 := by
      constructor
      · intro hs_left
        rcases hchain_top with htop_left | htop_right
        · exact htop_left
        · have hleft_childs : ∀ t, t ∈ (chain n).1 → t ∈ G.children level cell := by
            intro t ht
            exact (H.binaryRefinement.childs_are_children level cell hcell t).1
              ((T.TreeStructureChilds (chain n) hbranch_n).1 ht)
          have hs_mem_left : s ∈ (chain n).1 :=
            (child_subset_branchSupport_iff_mem G hs_child hleft_childs).1 hs_left
          have hs_mem_right : s ∈ (chain n).2 := by simp [← htop_right]
          exact (Finset.disjoint_left.mp
            (T.DisjointComponents (chain n) hbranch_n) hs_mem_left hs_mem_right).elim
      · intro htop_left
        have hs_mem_left : s ∈ (chain n).1 := by simp [← htop_left]
        exact subset_branchSupport_of_mem hs_mem_left
    simp [term, hleft_iff]
  have hsum_chain :
      (fun x =>
        ∑ i ∈ Finset.range n,
          (if Combinatorial_Support (chain (i + 1)) = (chain i).1 then
              (G.μ (branchSupport (chain i).2)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal
            else
              -((G.μ (branchSupport (chain i).1)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal))
            * haarWavelet G.μ (branchSupport (chain i).1) (branchSupport (chain i).2) x
        +
        (if ({s} : Finset (Set α)) = (chain n).1 then
            (G.μ (branchSupport (chain n).2)).toReal /
              (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal
          else
            -((G.μ (branchSupport (chain n).1)).toReal /
              (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal))
          * haarWavelet G.μ (branchSupport (chain n).1) (branchSupport (chain n).2) x)
        =
      (fun x => ∑ i ∈ Finset.range (n + 1), term (chain i) x) := by
    funext x
    rw [Finset.sum_range_succ]
    simp_rw [hcoeff_last]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt : i < n := by simpa [Finset.mem_range] using hi
    exact congrFun (hcoeff_step i hi_lt) x |>.symm
  calc
    (fun x =>
      Set.indicator s (fun _ => 1 / (G.μ s).toReal) x
      -
      Set.indicator cell (fun _ => 1 / (G.μ cell).toReal) x)
        =
      (fun x =>
        ∑ i ∈ Finset.range n,
          (if Combinatorial_Support (chain (i + 1)) = (chain i).1 then
              (G.μ (branchSupport (chain i).2)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal
            else
              -((G.μ (branchSupport (chain i).1)).toReal /
                (G.μ (branchSupport (Combinatorial_Support (chain i)))).toReal))
            * haarWavelet G.μ (branchSupport (chain i).1) (branchSupport (chain i).2) x
        +
        (if ({s} : Finset (Set α)) = (chain n).1 then
            (G.μ (branchSupport (chain n).2)).toReal /
              (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal
          else
            -((G.μ (branchSupport (chain n).1)).toReal /
              (G.μ (branchSupport (Combinatorial_Support (chain n)))).toReal))
          * haarWavelet G.μ (branchSupport (chain n).1) (branchSupport (chain n).2) x) := by
        funext x
        have hx := congrFun hchain_sum x
        rw [hx]
        ring
    _ = (fun x => ∑ i ∈ Finset.range (n + 1), term (chain i) x) := hsum_chain
    _ = (fun x => ∑ B ∈ F, term B x) := hsum_bij
    _ =
      (fun x =>
        ∑ B ∈
          ((H.binaryRefinement.tree level cell hcell).Branches).filter
            (fun B => s ⊆ branchSupport (Combinatorial_Support B)),
          (if s ⊆ branchSupport B.1 then
              (G.μ (branchSupport B.2)).toReal /
                (G.μ (branchSupport (Combinatorial_Support B))).toReal
            else
              -((G.μ (branchSupport B.1)).toReal /
                (G.μ (branchSupport (Combinatorial_Support B))).toReal))
            * haarWavelet G.μ (branchSupport B.1) (branchSupport B.2) x) := by
        rfl



/--
Important bridge theorem: any normalized partition indicator equals the
normalized alpha function plus a finite Haar-wavelet correction.

This is one of the main expansions used later in span and density arguments.
-/
theorem Normalized_indicator_in_Haar_Wavelets_span
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (s : Set α) (level : ℕ) (hs : s ∈ G.grid.partitions level) :
    (fun x => Set.indicator s (fun _ => 1 / (G.μ s).toReal) x)
      =
    (fun x => normalizedAlphaFunction G x + sumDown_normed_indicator G H s level hs x) := by
  classical
  induction level generalizing s with
  | zero =>
      have hs_univ : s = Set.univ := by
        simpa [G.grid.first_partition_eq_univ] using hs
      funext x
      simp [sumDown_normed_indicator, normalizedAlphaFunction, hs_univ]
  | succ n ih =>
      obtain ⟨parent, hparent, hs_parent⟩ := G.grid.nested n s hs
      have hs_child : s ∈ G.children n parent := ⟨hs, hs_parent⟩
      have hstep :=
        normalized_indicator_child_eq_cell_add_sum_chain_2
          (G := G) (H := H) (hcell := hparent) hs_child
      have hparent_exp := ih parent hparent
      have htarget_support_iff :
          ∀ {i : ℕ}, i < n →
          ∀ (c : {c : Set α // c ∈ G.grid.partitions i}),
          parent ⊆ c.1 →
          ∀ {A : Finset (Set α)},
          (∀ d, d ∈ A → d ∈ G.children i c.1) →
          (s ⊆ branchSupport A ↔ parent ⊆ branchSupport A) := by
        intro i hi_lt c hc_parent A hA_childs
        constructor
        · intro hsA
          obtain ⟨y, hy⟩ := G.partition_nonempty (n + 1) s hs
          have hyA : y ∈ branchSupport A := hsA hy
          rcases (by simpa [branchSupport] using hyA) with ⟨d, hdA, hyd⟩
          have hd_child : d ∈ G.children i c.1 := hA_childs d hdA
          have hi1_le_n : i + 1 ≤ n := by omega
          have hparent_d_or_disj :=
            G.partition_subset_or_disjoint_of_le (i + 1) n hi1_le_n
              d hd_child.1 parent hparent
          rcases hparent_d_or_disj with hparent_d | hparent_disj_d
          · exact hparent_d.trans (subset_branchSupport_of_mem hdA)
          · have hy_parent : y ∈ parent := hs_parent hy
            exact False.elim ((Set.disjoint_left.mp hparent_disj_d) hy_parent hyd)
        · intro hpA
          exact hs_parent.trans hpA
      have hsubtree_same :
          ∀ {i : ℕ}, i < n →
          ∀ (c : {c : Set α // c ∈ G.grid.partitions i}),
          parent ⊆ c.1 →
          sumDownSubTree_normed_indicator G H c.2 s =
            sumDownSubTree_normed_indicator G H c.2 parent := by
        intro i hi_lt c hc_parent
        funext x
        let Tanc := H.binaryRefinement.tree i c.1 c.2
        unfold sumDownSubTree_normed_indicator
        apply Finset.sum_congr
        · ext B
          constructor
          · intro hBf
            have hB : B ∈ Tanc.Branches := (Finset.mem_filter.mp hBf).1
            have hsB : s ⊆ branchSupport (Combinatorial_Support B) :=
              (Finset.mem_filter.mp hBf).2
            have hB_childs :
                ∀ d, d ∈ Combinatorial_Support B → d ∈ G.children i c.1 := by
              intro d hd
              have hchilds := Tanc.TreeStructureChilds B hB
              rcases Finset.mem_union.mp (by simpa [Combinatorial_Support] using hd) with hd1 | hd2
              · exact (H.binaryRefinement.childs_are_children i c.1 c.2 d).1 (hchilds.1 hd1)
              · exact (H.binaryRefinement.childs_are_children i c.1 c.2 d).1 (hchilds.2 hd2)
            exact Finset.mem_filter.mpr
              ⟨hB, (htarget_support_iff hi_lt c hc_parent hB_childs).1 hsB⟩
          · intro hBf
            have hB : B ∈ Tanc.Branches := (Finset.mem_filter.mp hBf).1
            have hpB : parent ⊆ branchSupport (Combinatorial_Support B) :=
              (Finset.mem_filter.mp hBf).2
            have hB_childs :
                ∀ d, d ∈ Combinatorial_Support B → d ∈ G.children i c.1 := by
              intro d hd
              have hchilds := Tanc.TreeStructureChilds B hB
              rcases Finset.mem_union.mp (by simpa [Combinatorial_Support] using hd) with hd1 | hd2
              · exact (H.binaryRefinement.childs_are_children i c.1 c.2 d).1 (hchilds.1 hd1)
              · exact (H.binaryRefinement.childs_are_children i c.1 c.2 d).1 (hchilds.2 hd2)
            exact Finset.mem_filter.mpr
              ⟨hB, (htarget_support_iff hi_lt c hc_parent hB_childs).2 hpB⟩
        · intro B hBf
          have hB : B ∈ Tanc.Branches := (Finset.mem_filter.mp hBf).1
          have hleft_childs : ∀ d, d ∈ B.1 → d ∈ G.children i c.1 := by
            intro d hd
            exact (H.binaryRefinement.childs_are_children i c.1 c.2 d).1
              ((Tanc.TreeStructureChilds B hB).1 hd)
          have hleft_iff :
              s ⊆ branchSupport B.1 ↔ parent ⊆ branchSupport B.1 :=
            htarget_support_iff hi_lt c hc_parent hleft_childs
          by_cases hsleft : s ⊆ branchSupport B.1
          · have hpleft : parent ⊆ branchSupport B.1 := hleft_iff.1 hsleft
            simp [hsleft, hpleft]
          · have hpnot : ¬ parent ⊆ branchSupport B.1 := by
              intro hpleft
              exact hsleft (hleft_iff.2 hpleft)
            simp [hsleft, hpnot]
      have hsum_succ :
          sumDown_normed_indicator G H s (n + 1) hs
            =
          (fun x =>
            sumDown_normed_indicator G H parent n hparent x
            + sumDownSubTree_normed_indicator G H hparent s x) := by
        funext x
        simp [sumDown_normed_indicator, Finset.sum_range_succ]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          have hi_lt_n : i < n := by simpa [Finset.mem_range] using hi
          apply Finset.sum_congr
          · ext c
            simp only [Finset.mem_filter, Finset.mem_attach, true_and]
            constructor
            · intro hs_c
              have hi_le_n : i ≤ n := Nat.le_of_lt hi_lt_n
              have hpc_or_disj :=
                G.partition_subset_or_disjoint_of_le i n hi_le_n c.1 c.2 parent hparent
              rcases hpc_or_disj with hp_sub_c | hp_disj_c
              · exact hp_sub_c
              · obtain ⟨y, hy⟩ := G.partition_nonempty (n + 1) s hs
                have hy_parent : y ∈ parent := hs_parent hy
                have hy_c : y ∈ c.1 := hs_c hy
                exact False.elim ((Set.disjoint_left.mp hp_disj_c) hy_parent hy_c)
            · intro hp_c
              exact hs_parent.trans hp_c
          · intro c hc
            have hc_parent : parent ⊆ c.1 := by
              exact (Finset.mem_filter.mp hc).2
            exact congrFun (hsubtree_same hi_lt_n c hc_parent) x
        · have hfilter_singleton :
            ((G.grid.partitions n).attach.filter (fun c => s ⊆ c.1)) =
              {⟨parent, hparent⟩} := by
            ext c
            simp only [Finset.mem_filter, Finset.mem_attach, true_and, Finset.mem_singleton]
            constructor
            · intro hs_c
              apply Subtype.ext
              have hc_eq_parent : c.1 = parent := by
                by_contra hne
                have hdisj := G.grid.disjoint n c.1 parent c.2 hparent hne
                obtain ⟨y, hy⟩ := G.partition_nonempty (n + 1) s hs
                have hy_c : y ∈ c.1 := hs_c hy
                have hy_parent : y ∈ parent := hs_parent hy
                exact (Set.disjoint_left.mp hdisj hy_c hy_parent).elim
              exact hc_eq_parent
            · intro hc_eq
              rw [hc_eq]
              exact hs_parent
          rw [hfilter_singleton]
          simp
      funext x
      have hstep_x := congrFun hstep x
      have hparent_x := congrFun hparent_exp x
      have hsum_x := congrFun hsum_succ x
      rw [hsum_x]
      calc
        Set.indicator s (fun _ => 1 / (G.μ s).toReal) x
            =
          Set.indicator parent (fun _ => 1 / (G.μ parent).toReal) x
            +
          (Set.indicator s (fun _ => 1 / (G.μ s).toReal) x
            - Set.indicator parent (fun _ => 1 / (G.μ parent).toReal) x) := by
            ring
        _ =
          (normalizedAlphaFunction G x + sumDown_normed_indicator G H parent n hparent x)
            + sumDownSubTree_normed_indicator G H hparent s x := by
            rw [hstep_x, hparent_x]
        _ =
          normalizedAlphaFunction G x
            + (sumDown_normed_indicator G H parent n hparent x
              + sumDownSubTree_normed_indicator G H hparent s x) := by
            ring

/--
Very important global span result: every partition indicator lies in the
linear span of the full Haar system.

This theorem is a key ingredient later used to prove density in `Lp`.
-/
theorem indicator_partition_mem_span_FullHaarSystem
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (s : Set α) (level : ℕ) (hs : s ∈ G.grid.partitions level) :
    (fun x => Set.indicator s (fun _ => (1 : ℝ)) x)
      ∈ Submodule.span ℝ (Set.range (FullHaarSystem.function G F)) := by
  classical
  let M : Submodule ℝ (α → ℝ) := Submodule.span ℝ (Set.range (FullHaarSystem.function G F))
  have halpha_mem : normalizedAlphaFunction G ∈ M := by
    have halpha : FullHaarSystem.function G F .alpha ∈ M :=
      Submodule.subset_span ⟨.alpha, rfl⟩
    simpa [FullHaarSystem.function, F.alphaFunction_def] using halpha
  have hwavelet_mem :
      ∀ {level : ℕ} {cell : Set α} (hcell : cell ∈ G.grid.partitions level)
        (r : Finset (Set α) × Finset (Set α))
        (hr : r ∈ (F.toHaarSystem.binaryRefinement.tree level cell hcell).Branches),
        haarWavelet G.μ (branchSupport r.1) (branchSupport r.2) ∈ M := by
    intro level cell hcell r hr
    let i : F.toHaarSystem.Index :=
      ⟨level, cell, hcell, ⟨r, hr⟩⟩
    have hi_mem : FullHaarSystem.function G F (.wavelet i) ∈ M :=
      Submodule.subset_span ⟨.wavelet i, rfl⟩
    have hi_mem' : HaarSystem.wavelet G F.toHaarSystem i ∈ M := by
      simpa [FullHaarSystem.function] using hi_mem
    rw [HaarSystem.wavelet, F.toHaarSystem.haarWavelets_def level cell hcell ⟨r, hr⟩] at hi_mem'
    exact hi_mem'
  have hsubtree_mem :
      ∀ {level : ℕ} {cell : Set α} (hcell : cell ∈ G.grid.partitions level) (u : Set α),
        sumDownSubTree_normed_indicator G F.toHaarSystem hcell u ∈ M := by
    intro level cell hcell u
    have hsum :
      (∑ B ∈
          ((F.toHaarSystem.binaryRefinement.tree level cell hcell).Branches).filter
            (fun B => u ⊆ branchSupport (Combinatorial_Support B)),
        fun x =>
          (if u ⊆ branchSupport B.1 then
              (G.μ (branchSupport B.2)).toReal /
                (G.μ (branchSupport (Combinatorial_Support B))).toReal
            else
              -((G.μ (branchSupport B.1)).toReal /
                (G.μ (branchSupport (Combinatorial_Support B))).toReal)) *
            haarWavelet G.μ (branchSupport B.1) (branchSupport B.2) x) ∈ M := by
      refine Submodule.sum_mem M ?_
      intro B hB
      have hBranch : B ∈ (F.toHaarSystem.binaryRefinement.tree level cell hcell).Branches :=
        (Finset.mem_filter.mp hB).1
      by_cases hu : u ⊆ branchSupport B.1
      · simp [hu]
        exact M.smul_mem _ (hwavelet_mem hcell B hBranch)
      · simp [hu]
        exact M.neg_mem (M.smul_mem _ (hwavelet_mem hcell B hBranch))
    have hrewrite :
        sumDownSubTree_normed_indicator G F.toHaarSystem hcell u =
          ∑ B ∈
            ((F.toHaarSystem.binaryRefinement.tree level cell hcell).Branches).filter
              (fun B => u ⊆ branchSupport (Combinatorial_Support B)),
            fun x =>
              (if u ⊆ branchSupport B.1 then
                  (G.μ (branchSupport B.2)).toReal /
                    (G.μ (branchSupport (Combinatorial_Support B))).toReal
                else
                  -((G.μ (branchSupport B.1)).toReal /
                    (G.μ (branchSupport (Combinatorial_Support B))).toReal)) *
                haarWavelet G.μ (branchSupport B.1) (branchSupport B.2) x := by
      funext x
      rw [Finset.sum_apply]
      rfl
    rw [hrewrite]
    exact hsum
  have hsum_mem : sumDown_normed_indicator G F.toHaarSystem s level hs ∈ M := by
    have hsum :
      (∑ i ∈ Finset.range level,
        ∑ c ∈ (G.grid.partitions i).attach.filter (fun c => s ⊆ c.1),
          sumDownSubTree_normed_indicator G F.toHaarSystem c.2 s) ∈ M := by
      refine Submodule.sum_mem M ?_
      intro i hi
      refine Submodule.sum_mem M ?_
      intro c hc
      exact hsubtree_mem c.2 s
    have hrewrite :
        sumDown_normed_indicator G F.toHaarSystem s level hs =
          ∑ i ∈ Finset.range level,
            ∑ c ∈ (G.grid.partitions i).attach.filter (fun c => s ⊆ c.1),
              sumDownSubTree_normed_indicator G F.toHaarSystem c.2 s := by
      funext x
      simp [sumDown_normed_indicator, Finset.sum_apply]
    rw [hrewrite]
    exact hsum
  have hnormalized_mem :
      (fun x => Set.indicator s (fun _ => 1 / (G.μ s).toReal) x) ∈ M := by
    rw [Normalized_indicator_in_Haar_Wavelets_span G F.toHaarSystem s level hs]
    exact M.add_mem halpha_mem hsum_mem
  have hμs_pos : 0 < G.μ s := G.positive_measure level s hs
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  have hμs_ne_zero : (G.μ s).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨by exact ne_of_gt hμs_pos, (MeasureTheory.measure_lt_top G.μ s).ne⟩
  have hscale :
      (G.μ s).toReal • (fun x => Set.indicator s (fun _ => 1 / (G.μ s).toReal) x)
        = (fun x => Set.indicator s (fun _ => (1 : ℝ)) x) := by
    funext x
    by_cases hx : x ∈ s
    · simp [Pi.smul_apply, Set.indicator_of_mem, hx, hμs_ne_zero]
    · simp [Pi.smul_apply, Set.indicator_of_notMem, hx]
  have hscaled_mem :
      (G.μ s).toReal • (fun x => Set.indicator s (fun _ => 1 / (G.μ s).toReal) x) ∈ M :=
    M.smul_mem _ hnormalized_mem
  simpa [M] using hscale ▸ hscaled_mem





/-- If `s` is a child of the grid cell `cell`, then the characteristic function of `s`
belongs to the linear span of the characteristic function of `cell` together with the Haar
wavelets coming from the binary refinement tree attached to `cell`.  The proof follows the
chain from the root of the refinement tree to the top `{s}` and applies the explicit
left/right one-step identities at each branch. -/
theorem indicator_child_mem_span_cell_and_refinement_haarWavelets
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell s : Set α} (hcell : cell ∈ G.grid.partitions level)
    (hs_child : s ∈ G.children level cell) :
    (fun x => Set.indicator s (fun _ => (1 : ℝ)) x)
      ∈
    Submodule.span ℝ
      ({fun x => Set.indicator cell (fun _ => (1 : ℝ)) x} ∪
        {f : α → ℝ |
          ∃ r : Finset (Set α) × Finset (Set α),
            ∃ hr : r ∈ (H.binaryRefinement.tree level cell hcell).Branches,
              f = H.haarWavelets level cell hcell ⟨r, hr⟩}) := by
  classical
  let T := H.binaryRefinement.tree level cell hcell
  let gens : Set (α → ℝ) :=
    {fun x => Set.indicator cell (fun _ => (1 : ℝ)) x} ∪
      {f : α → ℝ |
        ∃ r : Finset (Set α) × Finset (Set α),
          ∃ hr : r ∈ T.Branches,
            f = H.haarWavelets level cell hcell ⟨r, hr⟩}
  let M : Submodule ℝ (α → ℝ) := Submodule.span ℝ gens
  change (fun x => Set.indicator s (fun _ => (1 : ℝ)) x) ∈ M
  have hhaar_mem :
      ∀ r (hr : r ∈ T.Branches),
        haarWavelet G.μ (branchSupport r.1) (branchSupport r.2) ∈ M := by
    intro r hr
    have hgen :
        H.haarWavelets level cell hcell ⟨r, hr⟩ ∈ gens := by
      exact Or.inr ⟨r, hr, rfl⟩
    have hmem : H.haarWavelets level cell hcell ⟨r, hr⟩ ∈ M :=
      Submodule.subset_span hgen
    simpa [M, H.haarWavelets_def level cell hcell ⟨r, hr⟩] using hmem
  have hcell_mem :
      (fun x => Set.indicator cell (fun _ => (1 : ℝ)) x) ∈ M := by
    exact Submodule.subset_span (by exact Or.inl rfl)
  have hs_top : s ∈ T.Tops :=
    (H.binaryRefinement.tops_are_children level cell hcell s).2 hs_child
  rcases exists_chain_from_root_to_top (T := T) hs_top with
    ⟨n, chain, hchain_zero, hchain_top, hchain_mem, hchain_step⟩
  have hbranch_support_mem :
      ∀ i, i ≤ n →
        (fun x =>
          Set.indicator (branchSupport (Combinatorial_Support (chain i)))
            (fun _ => (1 : ℝ)) x) ∈ M := by
    intro i
    induction i with
    | zero =>
        intro _hi
        have hroot :
            branchSupport (Combinatorial_Support (chain 0)) = cell := by
          rw [hchain_zero]
          exact branchSupport_root_eq_cell G H
        simpa [hroot] using hcell_mem
    | succ i ih =>
        intro hi_succ
        have hi_le : i ≤ n := by omega
        have hi_lt : i < n := by omega
        have hparent_mem := ih hi_le
        have hstep := hchain_step i hi_lt
        have hparent_union :
            branchSupport ((chain i).1 ∪ (chain i).2)
              = branchSupport (Combinatorial_Support (chain i)) := by
          rfl
        have hbranch_i : chain i ∈ T.Branches := hchain_mem i hi_le
        have hhaar_i :
            haarWavelet G.μ (branchSupport (chain i).1) (branchSupport (chain i).2) ∈ M :=
          hhaar_mem (chain i) hbranch_i
        rcases hstep with hleft | hright
        · have hbasic := LinearCombinationRefinementTreeBasic
            (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell)
            (r := chain i) hbranch_i
          have hcomb :
              (fun x =>
                ((G.μ (branchSupport (chain i).1)).toReal /
                    ((G.μ (branchSupport (chain i).1)).toReal +
                      (G.μ (branchSupport (chain i).2)).toReal)) *
                  Set.indicator (branchSupport ((chain i).1 ∪ (chain i).2))
                    (fun _ => (1 : ℝ)) x
                +
                (((G.μ (branchSupport (chain i).1)).toReal *
                    (G.μ (branchSupport (chain i).2)).toReal) /
                    ((G.μ (branchSupport (chain i).1)).toReal +
                      (G.μ (branchSupport (chain i).2)).toReal)) *
                  haarWavelet G.μ
                    (branchSupport (chain i).1) (branchSupport (chain i).2) x) ∈ M := by
            exact M.add_mem
              (by
                simpa [Pi.smul_apply, hparent_union] using
                  M.smul_mem
                    (((G.μ (branchSupport (chain i).1)).toReal /
                      ((G.μ (branchSupport (chain i).1)).toReal +
                        (G.μ (branchSupport (chain i).2)).toReal)))
                    hparent_mem)
              (by
                simpa [Pi.smul_apply] using
                  M.smul_mem
                    ((((G.μ (branchSupport (chain i).1)).toReal *
                      (G.μ (branchSupport (chain i).2)).toReal) /
                      ((G.μ (branchSupport (chain i).1)).toReal +
                        (G.μ (branchSupport (chain i).2)).toReal)))
                    hhaar_i)
          have hside_mem :
              (fun x => Set.indicator (branchSupport (chain i).1)
                (fun _ => (1 : ℝ)) x) ∈ M := by
            simpa [hbasic] using hcomb
          simpa [hleft] using hside_mem
        · have hbasic := LinearCombinationRefinementTreeBasicRight
            (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell)
            (r := chain i) hbranch_i
          have hcomb :
              (fun x =>
                ((G.μ (branchSupport (chain i).2)).toReal /
                    ((G.μ (branchSupport (chain i).1)).toReal +
                      (G.μ (branchSupport (chain i).2)).toReal)) *
                  Set.indicator (branchSupport ((chain i).1 ∪ (chain i).2))
                    (fun _ => (1 : ℝ)) x
                -
                (((G.μ (branchSupport (chain i).1)).toReal *
                    (G.μ (branchSupport (chain i).2)).toReal) /
                    ((G.μ (branchSupport (chain i).1)).toReal +
                      (G.μ (branchSupport (chain i).2)).toReal)) *
                  haarWavelet G.μ
                    (branchSupport (chain i).1) (branchSupport (chain i).2) x) ∈ M := by
            exact M.sub_mem
              (by
                simpa [Pi.smul_apply, hparent_union] using
                  M.smul_mem
                    (((G.μ (branchSupport (chain i).2)).toReal /
                      ((G.μ (branchSupport (chain i).1)).toReal +
                        (G.μ (branchSupport (chain i).2)).toReal)))
                    hparent_mem)
              (by
                simpa [Pi.smul_apply] using
                  M.smul_mem
                    ((((G.μ (branchSupport (chain i).1)).toReal *
                      (G.μ (branchSupport (chain i).2)).toReal) /
                      ((G.μ (branchSupport (chain i).1)).toReal +
                        (G.μ (branchSupport (chain i).2)).toReal)))
                    hhaar_i)
          have hside_mem :
              (fun x => Set.indicator (branchSupport (chain i).2)
                (fun _ => (1 : ℝ)) x) ∈ M := by
            simpa [hbasic] using hcomb
          simpa [hright] using hside_mem
  have hn_mem := hbranch_support_mem n le_rfl
  have hbranch_n : chain n ∈ T.Branches := hchain_mem n le_rfl
  have hhaar_n :
      haarWavelet G.μ (branchSupport (chain n).1) (branchSupport (chain n).2) ∈ M :=
    hhaar_mem (chain n) hbranch_n
  rcases hchain_top with htop_left | htop_right
  · have hbasic := LinearCombinationRefinementTreeBasic
      (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell)
      (r := chain n) hbranch_n
    have hparent_union :
        branchSupport ((chain n).1 ∪ (chain n).2)
          = branchSupport (Combinatorial_Support (chain n)) := by
      rfl
    have hcomb :
        (fun x =>
          ((G.μ (branchSupport (chain n).1)).toReal /
              ((G.μ (branchSupport (chain n).1)).toReal +
                (G.μ (branchSupport (chain n).2)).toReal)) *
            Set.indicator (branchSupport ((chain n).1 ∪ (chain n).2))
              (fun _ => (1 : ℝ)) x
          +
          (((G.μ (branchSupport (chain n).1)).toReal *
              (G.μ (branchSupport (chain n).2)).toReal) /
              ((G.μ (branchSupport (chain n).1)).toReal +
                (G.μ (branchSupport (chain n).2)).toReal)) *
            haarWavelet G.μ
              (branchSupport (chain n).1) (branchSupport (chain n).2) x) ∈ M := by
      exact M.add_mem
        (by
          simpa [Pi.smul_apply, hparent_union] using
            M.smul_mem
              (((G.μ (branchSupport (chain n).1)).toReal /
                ((G.μ (branchSupport (chain n).1)).toReal +
                  (G.μ (branchSupport (chain n).2)).toReal)))
              hn_mem)
        (by
          simpa [Pi.smul_apply] using
            M.smul_mem
              ((((G.μ (branchSupport (chain n).1)).toReal *
                (G.μ (branchSupport (chain n).2)).toReal) /
                ((G.μ (branchSupport (chain n).1)).toReal +
                  (G.μ (branchSupport (chain n).2)).toReal)))
              hhaar_n)
    have hside_mem :
        (fun x => Set.indicator (branchSupport (chain n).1)
          (fun _ => (1 : ℝ)) x) ∈ M := by
      simpa [hbasic] using hcomb
    have hsingle : branchSupport (chain n).1 = s := by
      rw [← htop_left]
      exact branchSupport_singleton s
    simpa [hsingle] using hside_mem
  · have hbasic := LinearCombinationRefinementTreeBasicRight
      (G := G) (H := H) (level := level) (cell := cell) (hcell := hcell)
      (r := chain n) hbranch_n
    have hparent_union :
        branchSupport ((chain n).1 ∪ (chain n).2)
          = branchSupport (Combinatorial_Support (chain n)) := by
      rfl
    have hcomb :
        (fun x =>
          ((G.μ (branchSupport (chain n).2)).toReal /
              ((G.μ (branchSupport (chain n).1)).toReal +
                (G.μ (branchSupport (chain n).2)).toReal)) *
            Set.indicator (branchSupport ((chain n).1 ∪ (chain n).2))
              (fun _ => (1 : ℝ)) x
          -
          (((G.μ (branchSupport (chain n).1)).toReal *
              (G.μ (branchSupport (chain n).2)).toReal) /
              ((G.μ (branchSupport (chain n).1)).toReal +
                (G.μ (branchSupport (chain n).2)).toReal)) *
            haarWavelet G.μ
              (branchSupport (chain n).1) (branchSupport (chain n).2) x) ∈ M := by
      exact M.sub_mem
        (by
          simpa [Pi.smul_apply, hparent_union] using
            M.smul_mem
              (((G.μ (branchSupport (chain n).2)).toReal /
                ((G.μ (branchSupport (chain n).1)).toReal +
                  (G.μ (branchSupport (chain n).2)).toReal)))
              hn_mem)
        (by
          simpa [Pi.smul_apply] using
            M.smul_mem
              ((((G.μ (branchSupport (chain n).1)).toReal *
                (G.μ (branchSupport (chain n).2)).toReal) /
                ((G.μ (branchSupport (chain n).1)).toReal +
                  (G.μ (branchSupport (chain n).2)).toReal)))
              hhaar_n)
    have hside_mem :
        (fun x => Set.indicator (branchSupport (chain n).2)
          (fun _ => (1 : ℝ)) x) ∈ M := by
      simpa [hbasic] using hcomb
    have hsingle : branchSupport (chain n).2 = s := by
      rw [← htop_right]
      exact branchSupport_singleton s
    simpa [hsingle] using hside_mem




end UnbalancedHaarWavelet
