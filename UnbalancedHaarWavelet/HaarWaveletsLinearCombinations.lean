import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import UnbalancedHaarWavelet.GridDefinition
import UnbalancedHaarWavelet.HaarWaveletsDefinition

namespace UnbalancedHaarWavelet

variable {α : Type*} [MeasurableSpace α]

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

/-- For a branch `r = (A, B)` in the refinement tree, the characteristic function of the
support of `A` is the characteristic function of the support of `A ∪ B`, plus a scalar
multiple of the Haar wavelet associated with `(A, B)`. -/
lemma LinearCombinationRefinementTreeBasic
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level}
    {r : Finset (Set α) × Finset (Set α)}
    (hr : r ∈ (H.binaryRefinement.tree level cell hcell).Branches)
    (hA_ne : (G.μ (branchSupport r.1)).toReal ≠ 0)
    (hB_ne : (G.μ (branchSupport r.2)).toReal ≠ 0)
    (hsum_ne :
      (G.μ (branchSupport r.1)).toReal + (G.μ (branchSupport r.2)).toReal ≠ 0) :
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
  have hAB : Disjoint (branchSupport r.1) (branchSupport r.2) :=
    disjoint_branchSupport_of_finset_disjoint G level r.1 r.2 hA_part hB_part
      (T.DisjointComponents r hr)
  have hsupport_union :
      branchSupport (r.1 ∪ r.2) = branchSupport r.1 ∪ branchSupport r.2 := by
    ext x
    constructor
    · intro hx
      rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
      rcases hs with hsA | hsB
      · exact Or.inl (by
          simpa [branchSupport] using
            (show x ∈ ⋃ t ∈ (r.1 : Set (Set α)), t from
              Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hsA, hxs⟩⟩))
      · exact Or.inr (by
          simpa [branchSupport] using
            (show x ∈ ⋃ t ∈ (r.2 : Set (Set α)), t from
              Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hsB, hxs⟩⟩))
    · intro hx
      rcases hx with hxA | hxB
      · rcases (by simpa [branchSupport] using hxA) with ⟨s, hsA, hxs⟩
        simpa [branchSupport] using
          (show x ∈ ⋃ t ∈ ((r.1 ∪ r.2 : Finset (Set α)) : Set (Set α)), t from
            Set.mem_iUnion.2
              ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inl hsA), hxs⟩⟩)
      · rcases (by simpa [branchSupport] using hxB) with ⟨s, hsB, hxs⟩
        simpa [branchSupport] using
          (show x ∈ ⋃ t ∈ ((r.1 ∪ r.2 : Finset (Set α)) : Set (Set α)), t from
            Set.mem_iUnion.2
              ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inr hsB), hxs⟩⟩)
  simpa [hsupport_union] using
    indicator_left_eq_union_indicator_add_mul_haarWavelet
      G.μ (branchSupport r.1) (branchSupport r.2) hAB hA_ne hB_ne hsum_ne

end UnbalancedHaarWavelet
