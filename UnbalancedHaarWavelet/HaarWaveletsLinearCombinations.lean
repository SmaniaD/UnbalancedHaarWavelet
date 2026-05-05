import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Algebra.Module.Submodule.Basic
import UnbalancedHaarWavelet.GridDefinition
import UnbalancedHaarWavelet.HaarWaveletsDefinition

namespace UnbalancedHaarWavelet

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
    branchSupport (Combinatorial_Support T.Root)
        = branchSupport T.Childs := by rw [hroot_childs]
    _ = branchSupport (G.childrenFinset level cell) := by rw [hchilds_finset]
    _ = cell := branchSupport_childrenFinset_eq G level cell hcell

/-- Algebraic identity behind the refinement-tree linear combination: the indicator of the
left support `A` is a linear combination of the indicator of `A ∪ B` and the Haar wavelet
associated with the split `(A, B)`. -/
lemma indicator_left_eq_union_indicator_add_mul_haarWavelet
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
