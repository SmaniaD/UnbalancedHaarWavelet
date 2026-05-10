import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import UnbalancedHaarWavelet.GridDefinition

/-!
Core definitions for Haar systems on a grid.

This file builds the basic objects used everywhere else: branch supports, Haar
wavelets, indexed Haar families, and the full Haar system that includes the
normalized father function.
-/

namespace UnbalancedHaarWavelet

variable {α : Type*} [MeasurableSpace α]





/-- Existence of binary refinements of a  grid for any Grid. -/
theorem exists_binaryRefinementOfGrid
    (G : Grid (α := α)) [DecidableEq (Set α)]
    : Nonempty (BinaryRefinementOfGrid (G := G)) := by
  classical
  have hTree :
      ∀ n (Q : Set α) (hQ : Q ∈ G.grid.partitions n),
        ∃ T : BinaryTreeWithRootandTops (Set α),
          T.Childs = G.childrenFinset n Q ∧ T.Tops = G.childrenFinset n Q := by
    intro n Q hQ
    rcases exists_tree_childs_eq_C_and_all_childs_in_Tops_of_card_ge_two
        (C := G.childrenFinset n Q)
        (Grid.all_partition_elements_have_two_children G n Q hQ) with ⟨T, hChilds, hTops⟩
    exact ⟨T, hChilds, hTops.symm⟩
  choose tree hChilds hTops using hTree
  refine ⟨{
    tree := tree
    childs_are_children := ?_
    tops_are_children := ?_
    root_contains_children := ?_
  }⟩
  · intro n Q hQ s
    simpa [hChilds n Q hQ] using (G.mem_childrenFinset_iff n Q s)
  · intro n Q hQ s
    simpa [hTops n Q hQ] using (G.mem_childrenFinset_iff n Q s)
  · intro n Q hQ s hs
    have hs_child : s ∈ (tree n Q hQ).Childs := by
      simpa [hChilds n Q hQ] using (G.mem_childrenFinset_iff n Q s).2 hs
    exact (tree n Q hQ).RootcontainsChilds hs_child

/-- Support associated with a branch side `A`: union of the cells in `A`. -/
def branchSupport (A : Finset (Set α)) : Set α :=
  ⋃ s ∈ (A : Set (Set α)), s

omit [MeasurableSpace α] in
/-- Monotonicity of branch supports: if one side of a branch is included in another
as a finset of cells, then its union of cells is included in the other support. -/
lemma branchSupport_mono {A B : Finset (Set α)} (hAB : A ⊆ B) :
    branchSupport A ⊆ branchSupport B := by
  intro x hx
  rcases (by simpa [branchSupport] using hx) with ⟨s, hsA, hxs⟩
  have hsB : s ∈ B := hAB hsA
  exact by
    simpa [branchSupport] using (show x ∈ ⋃ t ∈ (B : Set (Set α)), t from
      Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hsB, hxs⟩⟩)

/-- Disjoint families of cells from the same partition level have disjoint branch supports.
This converts combinatorial disjointness of finite cell sets into set-theoretic disjointness
of their unions. -/
lemma disjoint_branchSupport_of_finset_disjoint
    (G : Grid (α := α))
    (n : ℕ) (A B : Finset (Set α))
    (hA_part : ∀ s, s ∈ A → s ∈ G.grid.partitions (n + 1))
    (hB_part : ∀ s, s ∈ B → s ∈ G.grid.partitions (n + 1))
    (hAB : Disjoint A B) :
    Disjoint (branchSupport A) (branchSupport B) := by
  refine Set.disjoint_left.2 ?_
  intro x hxA hxB
  rcases (by simpa [branchSupport] using hxA) with ⟨s, hsA, hxs⟩
  rcases (by simpa [branchSupport] using hxB) with ⟨t, htB, hxt⟩
  have hst_ne : s ≠ t := by
    intro hst
    have hs_not_mem_B : s ∉ B := (Finset.disjoint_left.mp hAB) hsA
    exact hs_not_mem_B (hst ▸ htB)
  have hst_disj : Disjoint s t :=
    G.grid.disjoint (n + 1) s t (hA_part s hsA) (hB_part t htB) hst_ne
  exact (Set.disjoint_left.mp hst_disj hxs hxt).elim

omit [MeasurableSpace α] in
/-- A cell belonging to a branch side is contained in the support of that side. -/
lemma subset_branchSupport_of_mem {A : Finset (Set α)} {s : Set α}
    (hs : s ∈ A) : s ⊆ branchSupport A := by
  intro x hx
  exact by
    simpa [branchSupport] using
      (show x ∈ ⋃ t ∈ (A : Set (Set α)), t from
        Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hs, hx⟩⟩)

/-- The support of a finite family of partition cells is measurable, since it is a finite
union of measurable partition elements. -/
lemma measurableSet_branchSupport_of_partition
    (G : Grid (α := α))
    (n : ℕ) (A : Finset (Set α))
    (hA_part : ∀ s, s ∈ A → s ∈ G.grid.partitions (n + 1)) :
    MeasurableSet (branchSupport A) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simp [branchSupport]
  | @insert a A ha ih =>
    have ha_part : a ∈ G.grid.partitions (n + 1) := hA_part a (by simp [ha])
    have ha_meas : MeasurableSet a := G.grid.measurable (n + 1) a ha_part
    have hA_part' : ∀ s, s ∈ A → s ∈ G.grid.partitions (n + 1) := by
      intro s hs
      exact hA_part s (by simp [hs])
    have hA_meas' : MeasurableSet (branchSupport A) := ih hA_part'
    have h_union : branchSupport (insert a A) = a ∪ branchSupport A := by
      ext x
      constructor
      · intro hx
        simp only [branchSupport, Set.mem_iUnion] at hx
        rcases hx with ⟨s, hs, hxs⟩
        rcases (Finset.mem_insert.mp hs) with rfl | hsA
        · exact Or.inl hxs
        · exact Or.inr (by
            simpa [branchSupport] using
              (show x ∈ ⋃ t ∈ (A : Set (Set α)), t from
                Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hsA, hxs⟩⟩))
      · intro hx
        rcases hx with hxa | hxA
        · simpa [branchSupport] using
            (show x ∈ ⋃ t ∈ ((insert a A : Finset (Set α)) : Set (Set α)), t from
              Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨by simp, hxa⟩⟩)
        · rcases (by simpa [branchSupport] using hxA) with ⟨s, hsA, hxs⟩
          simpa [branchSupport] using
            (show x ∈ ⋃ t ∈ ((insert a A : Finset (Set α)) : Set (Set α)), t from
              Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨by simp [hsA], hxs⟩⟩)
    rw [h_union]
    exact ha_meas.union hA_meas'

/-- A nonempty branch support has positive measure when every cell in the branch side has
positive measure. -/
lemma measure_branchSupport_pos_of_nonempty
    (G : Grid (α := α))
  (A : Finset (Set α))
    (hA_pos_cells : ∀ s, s ∈ A → 0 < G.μ s)
    (hA_nonempty : A.Nonempty) :
    0 < G.μ (branchSupport A) := by
  obtain ⟨s, hs⟩ := hA_nonempty
  have hs_sub : s ⊆ branchSupport A := subset_branchSupport_of_mem hs
  have hμs_pos : 0 < G.μ s := hA_pos_cells s hs
  have hμs_le : G.μ s ≤ G.μ (branchSupport A) := MeasureTheory.measure_mono hs_sub
  exact lt_of_lt_of_le hμs_pos hμs_le

/-- Haar wavelet associated with a branch split `(A, B)`:
`1_{S_A} / μ(S_A) - 1_{S_B} / μ(S_B)`. -/
noncomputable def haarWavelet
    (μ : MeasureTheory.Measure α) (A B : Set α) : α → ℝ :=
  fun x =>
    Set.indicator A
      (fun _ => 1 / (μ A).toReal) x
    -
    Set.indicator B
      (fun _ => 1 / (μ B).toReal) x



/-- A Haar system on a grid consists of a binary refinement at every partition cell and a
wavelet for each branch of each refinement tree, with those wavelets given by `haarWavelet`
on the two branch supports. -/
structure HaarSystem (G : Grid (α := α)) [DecidableEq (Set α)] where
  binaryRefinement : BinaryRefinementOfGrid G
  haarWavelets : ∀ n (Q : Set α) (hQ : Q ∈ G.grid.partitions n),
      {p : Finset (Set α) × Finset (Set α) //
        p ∈ (binaryRefinement.tree n Q hQ).Branches} → α → ℝ
  haarWavelets_def :
      ∀ n Q hQ
        (p : {p : Finset (Set α) × Finset (Set α) //
          p ∈ (binaryRefinement.tree n Q hQ).Branches}),
        haarWavelets n Q hQ p = haarWavelet G.μ (branchSupport p.1.1) (branchSupport p.1.2)

/-- Every grid admits a Haar system, obtained by choosing a binary refinement of the
children of each grid cell and assigning the canonical Haar wavelet to every branch. -/
theorem exists_haarSystem
    (G : Grid (α := α)) [DecidableEq (Set α)] :
    Nonempty (HaarSystem (G := G)) := by
  classical
  obtain ⟨R⟩ := exists_binaryRefinementOfGrid (G := G)
  exact ⟨{
    binaryRefinement := R
    haarWavelets := fun _ _ _ p =>
      haarWavelet G.μ (branchSupport p.1.1) (branchSupport p.1.2)
    haarWavelets_def := by
      intro n Q hQ p
      rfl
  }⟩

/-- The normalized father function `1_α / μ(α)`, written as indicator on `Set.univ`. -/
noncomputable def normalizedAlphaFunction
    (G : Grid (α := α)) : α → ℝ :=
  fun x =>
    Set.indicator (Set.univ : Set α)
      (fun _ => 1 / (G.μ Set.univ).toReal) x

/-- A full Haar system: a Haar system plus the normalized father function `1_α / μ(α)`. -/
structure FullHaarSystem (G : Grid (α := α)) [DecidableEq (Set α)] extends HaarSystem G where
  alphaFunction : α → ℝ
  alphaFunction_def : alphaFunction = normalizedAlphaFunction G



/-- A global index for Haar wavelets: it records the level, the partition cell at that level,
and one branch of the binary refinement tree for that cell. -/
structure HaarSystem.Index
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) where
  level : ℕ
  cell : Set α
  hcell : cell ∈ G.grid.partitions level
  branch : {r : Finset (Set α) × Finset (Set α) //
    r ∈ (H.binaryRefinement.tree level cell hcell).Branches}

/-- The actual Haar wavelet function selected by a global `HaarSystem.Index`. -/
def HaarSystem.wavelet
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) : α → ℝ :=
  H.haarWavelets i.level i.cell i.hcell i.branch



/-- Indices for the full Haar system: either the normalized father function or one ordinary
Haar wavelet index. -/
inductive FullHaarSystem.Index
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G)) where
  | alpha
  | wavelet (i : F.toHaarSystem.Index)

/-- The function selected by a full Haar-system index. -/
def FullHaarSystem.function
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (i : F.Index) : α → ℝ :=
  match i with
  | .alpha => F.alphaFunction
  | .wavelet j => HaarSystem.wavelet G F.toHaarSystem j

end UnbalancedHaarWavelet
