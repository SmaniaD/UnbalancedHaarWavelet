import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import UnbalancedHaarWavelet.GridDefinition
import UnbalancedHaarWavelet.HaarWaveletsDefinition

/-!
Support laminarity and the induced binary-grid structure attached to a Haar system.
-/
set_option linter.style.header false
set_option linter.style.openClassical false

namespace UnbalancedHaarWavelet

variable {α : Type*} [MeasurableSpace α]

open scoped Classical

/-- The set-theoretic support associated with a branch, i.e. the union of all grid cells
appearing in its two sides. -/
noncomputable def haarBranchSupport [DecidableEq (Set α)]
    (p : Finset (Set α) × Finset (Set α)) : Set α :=
  UnbalancedHaarWavelet.branchSupport (Combinatorial_Support p)

omit [MeasurableSpace α] in
lemma haarBranchSupport_subset_of_combinatorial_subset
    [DecidableEq (Set α)]
    {p q : Finset (Set α) × Finset (Set α)}
    (hpq : Combinatorial_Support p ⊆ Combinatorial_Support q) :
    haarBranchSupport p ⊆ haarBranchSupport q := by
  simpa [haarBranchSupport] using branchSupport_mono hpq

lemma haarBranchSupport_disjoint_of_combinatorial_disjoint
    (G : Grid (α := α)) [DecidableEq (Set α)]
    {n : ℕ} {p q : Finset (Set α) × Finset (Set α)}
    (hp_part : ∀ s, s ∈ Combinatorial_Support p → s ∈ G.grid.partitions (n + 1))
    (hq_part : ∀ s, s ∈ Combinatorial_Support q → s ∈ G.grid.partitions (n + 1))
    (hpq : Disjoint (Combinatorial_Support p) (Combinatorial_Support q)) :
    Disjoint (haarBranchSupport p) (haarBranchSupport q) := by
  simpa [haarBranchSupport] using
    disjoint_branchSupport_of_finset_disjoint
      G n (Combinatorial_Support p) (Combinatorial_Support q) hp_part hq_part hpq

/-- Positive measure of the support of a branch. -/
lemma measure_haarBranchSupport_pos
    (G : Grid (α := α)) [DecidableEq (Set α)]
    {n : ℕ} {T : BinaryTreeWithRootandTops (Set α)}
    {p : Finset (Set α) × Finset (Set α)}
    (hp : p ∈ T.Branches)
    (hp_part : ∀ s, s ∈ Combinatorial_Support p → s ∈ G.grid.partitions (n + 1)) :
    0 < G.μ (haarBranchSupport p) := by
  classical
  have hp_nonempty : (Combinatorial_Support p).Nonempty := by
    obtain ⟨s, hs⟩ := (T.NonemptyPairs p hp).1
    exact ⟨s, by
      dsimp [Combinatorial_Support]
      exact Finset.mem_union_left p.2 hs⟩
  simpa [haarBranchSupport] using
    measure_branchSupport_pos_of_nonempty G (Combinatorial_Support p)
      (by
        intro s hs
        exact G.positive_measure (n + 1) s (hp_part s hs))
      hp_nonempty

/-- The support of a branch in the binary refinement tree of a grid cell is contained in
that grid cell. -/
lemma HaarSystem.haarBranchSupport_subset_cell
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {n : ℕ} {Q : Set α} {hQ : Q ∈ G.grid.partitions n}
    (p : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches}) :
    haarBranchSupport p.1 ⊆ Q := by
  classical
  let T := H.binaryRefinement.tree n Q hQ
  have hp_childs : p.1.1 ⊆ T.Childs ∧ p.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds p.1 p.2
  intro x hx
  rcases (by simpa [haarBranchSupport, branchSupport, Combinatorial_Support] using hx)
    with ⟨s, hs, hxs⟩
  have hs_childs : s ∈ T.Childs := by
    rcases hs with hs1 | hs2
    · exact hp_childs.1 hs1
    · exact hp_childs.2 hs2
  have hs_child : s ∈ G.children n Q :=
    (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_childs
  exact hs_child.2 hxs

lemma HaarSystem.haarBranchSupport_disjoint_of_cells_disjoint
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {n m : ℕ} {Q P : Set α}
    {hQ : Q ∈ G.grid.partitions n} {hP : P ∈ G.grid.partitions m}
    (q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches})
    (p : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree m P hP).Branches})
    (hQP : Disjoint Q P) :
    Disjoint (haarBranchSupport q.1) (haarBranchSupport p.1) := by
  exact (hQP.mono_left (H.haarBranchSupport_subset_cell G q)).mono_right
    (H.haarBranchSupport_subset_cell G p)

lemma HaarSystem.measure_ne_of_subset_branchSupport_left
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {n : ℕ} {Q : Set α} {hQ : Q ∈ G.grid.partitions n}
    (q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches})
    {A : Set α}
    (hA_sub : A ⊆ UnbalancedHaarWavelet.branchSupport q.1.1) :
    G.μ A ≠ G.μ (haarBranchSupport q.1) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  let T := H.binaryRefinement.tree n Q hQ
  have hq_childs : q.1.1 ⊆ T.Childs ∧ q.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds q.1 q.2
  have hq1_part : ∀ s, s ∈ q.1.1 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.1 hs) |>.1
  have hq2_part : ∀ s, s ∈ q.1.2 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.2 hs) |>.1
  let B₁ := UnbalancedHaarWavelet.branchSupport q.1.1
  let B₂ := UnbalancedHaarWavelet.branchSupport q.1.2
  intro h_eq
  have hB₂_pos : 0 < G.μ B₂ := by
    exact measure_branchSupport_pos_of_nonempty G q.1.2
      (by
        intro s hs
        exact G.positive_measure (n + 1) s (hq2_part s hs))
      (T.NonemptyPairs q.1 q.2).2
  have hB₁B₂_disj : Disjoint B₁ B₂ :=
    disjoint_branchSupport_of_finset_disjoint G n q.1.1 q.1.2 hq1_part hq2_part
      (T.DisjointComponents q.1 q.2)
  have hA_B₂_disj : Disjoint A B₂ := hB₁B₂_disj.mono_left hA_sub
  have hB₂_meas : MeasurableSet B₂ :=
    measurableSet_branchSupport_of_partition G n q.1.2 hq2_part
  have hA_union_B₂ :
      G.μ (A ∪ B₂) = G.μ A + G.μ B₂ :=
    MeasureTheory.measure_union hA_B₂_disj hB₂_meas
  have hA_union_B₂_subset : A ∪ B₂ ⊆ haarBranchSupport q.1 := by
    refine Set.union_subset ?_ ?_
    · exact hA_sub.trans (by
        intro x hx
        simpa [haarBranchSupport, B₁, branchSupport, Combinatorial_Support] using
          (show x ∈ ⋃ t ∈ ((q.1.1 ∪ q.1.2 : Finset (Set α)) : Set (Set α)), t from by
            rcases (by simpa [B₁, branchSupport] using hx) with ⟨s, hs, hxs⟩
            exact Set.mem_iUnion.2
              ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inl hs), hxs⟩⟩))
    · intro x hx
      simpa [haarBranchSupport, B₂, branchSupport, Combinatorial_Support] using
        (show x ∈ ⋃ t ∈ ((q.1.1 ∪ q.1.2 : Finset (Set α)) : Set (Set α)), t from by
          rcases (by simpa [B₂, branchSupport] using hx) with ⟨s, hs, hxs⟩
          exact Set.mem_iUnion.2
            ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inr hs), hxs⟩⟩)
  have hlt_union : G.μ A < G.μ (A ∪ B₂) := by
    rw [hA_union_B₂]
    exact ENNReal.lt_add_right (MeasureTheory.measure_ne_top G.μ A) hB₂_pos.ne'
  have hle_A : G.μ (A ∪ B₂) ≤ G.μ A := by
    calc
      G.μ (A ∪ B₂) ≤ G.μ (haarBranchSupport q.1) :=
        MeasureTheory.measure_mono hA_union_B₂_subset
      _ = G.μ A := h_eq.symm
  exact not_lt_of_ge hle_A hlt_union

lemma HaarSystem.measure_ne_of_subset_branchSupport_right
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {n : ℕ} {Q : Set α} {hQ : Q ∈ G.grid.partitions n}
    (q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches})
    {A : Set α}
    (hA_sub : A ⊆ UnbalancedHaarWavelet.branchSupport q.1.2) :
    G.μ A ≠ G.μ (haarBranchSupport q.1) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  let T := H.binaryRefinement.tree n Q hQ
  have hq_childs : q.1.1 ⊆ T.Childs ∧ q.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds q.1 q.2
  have hq1_part : ∀ s, s ∈ q.1.1 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.1 hs) |>.1
  have hq2_part : ∀ s, s ∈ q.1.2 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.2 hs) |>.1
  let B₁ := UnbalancedHaarWavelet.branchSupport q.1.1
  let B₂ := UnbalancedHaarWavelet.branchSupport q.1.2
  intro h_eq
  have hB₁_pos : 0 < G.μ B₁ := by
    exact measure_branchSupport_pos_of_nonempty G q.1.1
      (by
        intro s hs
        exact G.positive_measure (n + 1) s (hq1_part s hs))
      (T.NonemptyPairs q.1 q.2).1
  have hB₁B₂_disj : Disjoint B₁ B₂ :=
    disjoint_branchSupport_of_finset_disjoint G n q.1.1 q.1.2 hq1_part hq2_part
      (T.DisjointComponents q.1 q.2)
  have hA_B₁_disj : Disjoint A B₁ := hB₁B₂_disj.symm.mono_left hA_sub
  have hB₁_meas : MeasurableSet B₁ :=
    measurableSet_branchSupport_of_partition G n q.1.1 hq1_part
  have hA_union_B₁ :
      G.μ (A ∪ B₁) = G.μ A + G.μ B₁ :=
    MeasureTheory.measure_union hA_B₁_disj hB₁_meas
  have hA_union_B₁_subset : A ∪ B₁ ⊆ haarBranchSupport q.1 := by
    refine Set.union_subset ?_ ?_
    · exact hA_sub.trans (by
        intro x hx
        simpa [haarBranchSupport, B₂, branchSupport, Combinatorial_Support] using
          (show x ∈ ⋃ t ∈ ((q.1.1 ∪ q.1.2 : Finset (Set α)) : Set (Set α)), t from by
            rcases (by simpa [B₂, branchSupport] using hx) with ⟨s, hs, hxs⟩
            exact Set.mem_iUnion.2
              ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inr hs), hxs⟩⟩))
    · intro x hx
      simpa [haarBranchSupport, B₁, branchSupport, Combinatorial_Support] using
        (show x ∈ ⋃ t ∈ ((q.1.1 ∪ q.1.2 : Finset (Set α)) : Set (Set α)), t from by
          rcases (by simpa [B₁, branchSupport] using hx) with ⟨s, hs, hxs⟩
          exact Set.mem_iUnion.2
            ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inl hs), hxs⟩⟩)
  have hlt_union : G.μ A < G.μ (A ∪ B₁) := by
    rw [hA_union_B₁]
    exact ENNReal.lt_add_right (MeasureTheory.measure_ne_top G.μ A) hB₁_pos.ne'
  have hle_A : G.μ (A ∪ B₁) ≤ G.μ A := by
    calc
      G.μ (A ∪ B₁) ≤ G.μ (haarBranchSupport q.1) :=
        MeasureTheory.measure_mono hA_union_B₁_subset
      _ = G.μ A := h_eq.symm
  exact not_lt_of_ge hle_A hlt_union

/-- Laminarity of the supports of two branches in the same binary refinement tree.

The measure alternatives are stated as `≠`; in fact the proof gets strict inequality in the
nested direction from positivity of the missing side of the larger split. -/
theorem HaarSystem.haarBranchSupport_laminar_same_tree
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (n : ℕ) (Q : Set α) (hQ : Q ∈ G.grid.partitions n)
    (p q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches}) :
    p = q ∨
      (haarBranchSupport p.1 ⊆ haarBranchSupport q.1 ∧
        G.μ (haarBranchSupport p.1) ≠ G.μ (haarBranchSupport q.1)) ∨
      (haarBranchSupport q.1 ⊆ haarBranchSupport p.1 ∧
        G.μ (haarBranchSupport q.1) ≠ G.μ (haarBranchSupport p.1)) ∨
      Disjoint (haarBranchSupport p.1) (haarBranchSupport q.1) := by
  classical
  by_cases hpq : p = q
  · exact Or.inl hpq
  · right
    letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
    let T := H.binaryRefinement.tree n Q hQ
    have hpq_val : p.1 ≠ q.1 := by
      intro h
      exact hpq (Subtype.ext h)
    have hp_childs : p.1.1 ⊆ T.Childs ∧ p.1.2 ⊆ T.Childs :=
      T.TreeStructureChilds p.1 p.2
    have hq_childs : q.1.1 ⊆ T.Childs ∧ q.1.2 ⊆ T.Childs :=
      T.TreeStructureChilds q.1 q.2
    have hp_part : ∀ s, s ∈ Combinatorial_Support p.1 → s ∈ G.grid.partitions (n + 1) := by
      intro s hs
      rcases Finset.mem_union.mp (by simpa [Combinatorial_Support] using hs) with hs1 | hs2
      · exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hp_childs.1 hs1) |>.1
      · exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hp_childs.2 hs2) |>.1
    have hq_part : ∀ s, s ∈ Combinatorial_Support q.1 → s ∈ G.grid.partitions (n + 1) := by
      intro s hs
      rcases Finset.mem_union.mp (by simpa [Combinatorial_Support] using hs) with hs1 | hs2
      · exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.1 hs1) |>.1
      · exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.2 hs2) |>.1
    have hp1_part : ∀ s, s ∈ p.1.1 → s ∈ G.grid.partitions (n + 1) := by
      intro s hs
      exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hp_childs.1 hs) |>.1
    have hp2_part : ∀ s, s ∈ p.1.2 → s ∈ G.grid.partitions (n + 1) := by
      intro s hs
      exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hp_childs.2 hs) |>.1
    have hq1_part : ∀ s, s ∈ q.1.1 → s ∈ G.grid.partitions (n + 1) := by
      intro s hs
      exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.1 hs) |>.1
    have hq2_part : ∀ s, s ∈ q.1.2 → s ∈ G.grid.partitions (n + 1) := by
      intro s hs
      exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.2 hs) |>.1
    have hmeasure_ne_of_sub_left :
        ∀ {a b : Finset (Set α) × Finset (Set α)},
          a ∈ T.Branches → b ∈ T.Branches →
          (∀ s, s ∈ Combinatorial_Support a → s ∈ G.grid.partitions (n + 1)) →
          (∀ s, s ∈ b.1 → s ∈ G.grid.partitions (n + 1)) →
          (∀ s, s ∈ b.2 → s ∈ G.grid.partitions (n + 1)) →
          Combinatorial_Support a ⊆ b.1 →
          G.μ (haarBranchSupport a) ≠ G.μ (haarBranchSupport b) := by
      intro a b ha hb ha_part hb1_part hb2_part ha_sub_b1 h_eq
      let A := haarBranchSupport a
      let B₁ := UnbalancedHaarWavelet.branchSupport b.1
      let B₂ := UnbalancedHaarWavelet.branchSupport b.2
      have hA_sub_B₁ : A ⊆ B₁ := by
        simpa [A, haarBranchSupport] using branchSupport_mono ha_sub_b1
      have hB₂_pos : 0 < G.μ B₂ := by
        exact measure_branchSupport_pos_of_nonempty G b.2
          (by
            intro s hs
            exact G.positive_measure (n + 1) s (hb2_part s hs))
          (T.NonemptyPairs b hb).2
      have hB₁B₂_disj : Disjoint B₁ B₂ :=
        disjoint_branchSupport_of_finset_disjoint G n b.1 b.2 hb1_part hb2_part
          (T.DisjointComponents b hb)
      have hA_B₂_disj : Disjoint A B₂ := hB₁B₂_disj.mono_left hA_sub_B₁
      have hB₂_meas : MeasurableSet B₂ :=
        measurableSet_branchSupport_of_partition G n b.2 hb2_part
      have hA_union_B₂ :
          G.μ (A ∪ B₂) = G.μ A + G.μ B₂ :=
        MeasureTheory.measure_union hA_B₂_disj hB₂_meas
      have hA_union_B₂_subset : A ∪ B₂ ⊆ haarBranchSupport b := by
        refine Set.union_subset ?_ ?_
        · exact hA_sub_B₁.trans (by
            intro x hx
            simpa [haarBranchSupport, B₁, branchSupport, Combinatorial_Support] using
              (show x ∈ ⋃ t ∈ ((b.1 ∪ b.2 : Finset (Set α)) : Set (Set α)), t from by
                rcases (by simpa [B₁, branchSupport] using hx) with ⟨s, hs, hxs⟩
                exact Set.mem_iUnion.2
                  ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inl hs), hxs⟩⟩))
        · intro x hx
          simpa [haarBranchSupport, B₂, branchSupport, Combinatorial_Support] using
            (show x ∈ ⋃ t ∈ ((b.1 ∪ b.2 : Finset (Set α)) : Set (Set α)), t from by
              rcases (by simpa [B₂, branchSupport] using hx) with ⟨s, hs, hxs⟩
              exact Set.mem_iUnion.2
                ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inr hs), hxs⟩⟩)
      have hlt_union : G.μ A < G.μ (A ∪ B₂) := by
        rw [hA_union_B₂]
        exact ENNReal.lt_add_right (MeasureTheory.measure_ne_top G.μ A) hB₂_pos.ne'
      have hle_A : G.μ (A ∪ B₂) ≤ G.μ A := by
        calc
          G.μ (A ∪ B₂) ≤ G.μ (haarBranchSupport b) :=
            MeasureTheory.measure_mono hA_union_B₂_subset
          _ = G.μ A := h_eq.symm
      exact (not_lt_of_ge hle_A hlt_union)
    have hmeasure_ne_of_sub_right :
        ∀ {a b : Finset (Set α) × Finset (Set α)},
          a ∈ T.Branches → b ∈ T.Branches →
          (∀ s, s ∈ Combinatorial_Support a → s ∈ G.grid.partitions (n + 1)) →
          (∀ s, s ∈ b.1 → s ∈ G.grid.partitions (n + 1)) →
          (∀ s, s ∈ b.2 → s ∈ G.grid.partitions (n + 1)) →
          Combinatorial_Support a ⊆ b.2 →
          G.μ (haarBranchSupport a) ≠ G.μ (haarBranchSupport b) := by
      intro a b ha hb ha_part hb1_part hb2_part ha_sub_b2 h_eq
      let A := haarBranchSupport a
      let B₁ := UnbalancedHaarWavelet.branchSupport b.1
      let B₂ := UnbalancedHaarWavelet.branchSupport b.2
      have hA_sub_B₂ : A ⊆ B₂ := by
        simpa [A, haarBranchSupport] using branchSupport_mono ha_sub_b2
      have hB₁_pos : 0 < G.μ B₁ := by
        exact measure_branchSupport_pos_of_nonempty G b.1
          (by
            intro s hs
            exact G.positive_measure (n + 1) s (hb1_part s hs))
          (T.NonemptyPairs b hb).1
      have hB₁B₂_disj : Disjoint B₁ B₂ :=
        disjoint_branchSupport_of_finset_disjoint G n b.1 b.2 hb1_part hb2_part
          (T.DisjointComponents b hb)
      have hA_B₁_disj : Disjoint A B₁ := hB₁B₂_disj.symm.mono_left hA_sub_B₂
      have hB₁_meas : MeasurableSet B₁ :=
        measurableSet_branchSupport_of_partition G n b.1 hb1_part
      have hA_union_B₁ :
          G.μ (A ∪ B₁) = G.μ A + G.μ B₁ :=
        MeasureTheory.measure_union hA_B₁_disj hB₁_meas
      have hA_union_B₁_subset : A ∪ B₁ ⊆ haarBranchSupport b := by
        refine Set.union_subset ?_ ?_
        · exact hA_sub_B₂.trans (by
            intro x hx
            simpa [haarBranchSupport, B₂, branchSupport, Combinatorial_Support] using
              (show x ∈ ⋃ t ∈ ((b.1 ∪ b.2 : Finset (Set α)) : Set (Set α)), t from by
                rcases (by simpa [B₂, branchSupport] using hx) with ⟨s, hs, hxs⟩
                exact Set.mem_iUnion.2
                  ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inr hs), hxs⟩⟩))
        · intro x hx
          simpa [haarBranchSupport, B₁, branchSupport, Combinatorial_Support] using
            (show x ∈ ⋃ t ∈ ((b.1 ∪ b.2 : Finset (Set α)) : Set (Set α)), t from by
              rcases (by simpa [B₁, branchSupport] using hx) with ⟨s, hs, hxs⟩
              exact Set.mem_iUnion.2
                ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inl hs), hxs⟩⟩)
      have hlt_union : G.μ A < G.μ (A ∪ B₁) := by
        rw [hA_union_B₁]
        exact ENNReal.lt_add_right (MeasureTheory.measure_ne_top G.μ A) hB₁_pos.ne'
      have hle_A : G.μ (A ∪ B₁) ≤ G.μ A := by
        calc
          G.μ (A ∪ B₁) ≤ G.μ (haarBranchSupport b) :=
            MeasureTheory.measure_mono hA_union_B₁_subset
          _ = G.μ A := h_eq.symm
      exact (not_lt_of_ge hle_A hlt_union)
    rcases T.SupportProperty p.1 p.2 q.1 q.2 hpq_val with
      hdisj | hp_sub_q1 | hp_sub_q2 | hq_sub_p1 | hq_sub_p2
    · exact Or.inr (Or.inr
        (haarBranchSupport_disjoint_of_combinatorial_disjoint G hp_part hq_part hdisj)
      )
    · left
      exact ⟨
        haarBranchSupport_subset_of_combinatorial_subset
          (hp_sub_q1.trans (Finset.subset_union_left)),
        hmeasure_ne_of_sub_left p.2 q.2 hp_part hq1_part hq2_part hp_sub_q1⟩
    · left
      exact ⟨
        haarBranchSupport_subset_of_combinatorial_subset
          (hp_sub_q2.trans (Finset.subset_union_right)),
        hmeasure_ne_of_sub_right p.2 q.2 hp_part hq1_part hq2_part hp_sub_q2⟩
    · right
      left
      exact ⟨
        haarBranchSupport_subset_of_combinatorial_subset
          (hq_sub_p1.trans (Finset.subset_union_left)),
        hmeasure_ne_of_sub_left q.2 p.2 hq_part hp1_part hp2_part hq_sub_p1⟩
    · right
      left
      exact ⟨
        haarBranchSupport_subset_of_combinatorial_subset
          (hq_sub_p2.trans (Finset.subset_union_right)),
        hmeasure_ne_of_sub_right q.2 p.2 hq_part hp1_part hp2_part hq_sub_p2⟩

/-- In a fixed binary refinement tree, the set-theoretic branch support is injective on
branches. -/
theorem HaarSystem.haarBranchSupport_eq_iff_eq_same_tree
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (level : ℕ) (cell : Set α) (hcell : cell ∈ G.grid.partitions level)
    (p q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree level cell hcell).Branches}) :
    haarBranchSupport p.1 = haarBranchSupport q.1 ↔ p = q := by
  classical
  constructor
  · intro hsupport
    rcases H.haarBranchSupport_laminar_same_tree G level cell hcell p q with
      hpq | hsub | hsub | hdisj
    · exact hpq
    · rcases hsub with ⟨_hsubset, hmeasure_ne⟩
      exact (hmeasure_ne (by rw [hsupport])).elim
    · rcases hsub with ⟨_hsubset, hmeasure_ne⟩
      exact (hmeasure_ne (by rw [hsupport])).elim
    · have hself_disj : Disjoint (haarBranchSupport p.1) (haarBranchSupport p.1) := by
        simpa [hsupport] using hdisj
      let T := H.binaryRefinement.tree level cell hcell
      have hp_childs : p.1.1 ⊆ T.Childs ∧ p.1.2 ⊆ T.Childs :=
        T.TreeStructureChilds p.1 p.2
      have hp_part :
          ∀ s, s ∈ Combinatorial_Support p.1 → s ∈ G.grid.partitions (level + 1) := by
        intro s hs
        rcases Finset.mem_union.mp (by simpa [Combinatorial_Support] using hs) with hs1 | hs2
        · exact (H.binaryRefinement.childs_are_children level cell hcell s).1
            (hp_childs.1 hs1) |>.1
        · exact (H.binaryRefinement.childs_are_children level cell hcell s).1
            (hp_childs.2 hs2) |>.1
      have hpos : 0 < G.μ (haarBranchSupport p.1) :=
        measure_haarBranchSupport_pos G p.2 hp_part
      have hempty : haarBranchSupport p.1 = ∅ := by
        ext x
        constructor
        · intro hx
          exact (Set.disjoint_left.mp hself_disj hx hx).elim
        · intro hx
          exact False.elim (by simpa using hx)
      rw [hempty] at hpos
      simpa using hpos
  · intro hpq
    rw [hpq]

/-- The support of any branch in any refinement tree is nonempty. -/
lemma HaarSystem.haarBranchSupport_nonempty
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (level : ℕ) (cell : Set α) (hcell : cell ∈ G.grid.partitions level)
    (p : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree level cell hcell).Branches}) :
    (haarBranchSupport p.1).Nonempty := by
  classical
  let T := H.binaryRefinement.tree level cell hcell
  obtain ⟨s, hs⟩ := (T.NonemptyPairs p.1 p.2).1
  have hs_child : s ∈ T.Childs :=
    (T.TreeStructureChilds p.1 p.2).1 hs
  have hs_part : s ∈ G.grid.partitions (level + 1) :=
    (H.binaryRefinement.childs_are_children level cell hcell s).1 hs_child |>.1
  obtain ⟨x, hx⟩ := G.partition_nonempty (level + 1) s hs_part
  refine ⟨x, ?_⟩
  rw [haarBranchSupport, branchSupport, Combinatorial_Support]
  exact Set.mem_iUnion.2
    ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union_left p.1.2 hs, hx⟩⟩

/-- LongChain definition and consequences
A finite chain of branch supports, starting at the root branch of the unique cell in the
first partition and moving at each step into one side of the previous branch. -/
def LongChain_to_Root
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n : ℕ)
    (chain : ℕ → (Finset (Set α) × Finset (Set α))) : Prop :=
  chain 0 =
      (H.binaryRefinement.tree 0 Set.univ
        (by simp [G.grid.first_partition_eq_univ])).Root ∧
    (∀ i ≤ n, ∃ level : ℕ, ∃ cell : Set α, ∃ hcell : cell ∈ G.grid.partitions level,
      chain i ∈ (H.binaryRefinement.tree level cell hcell).Branches) ∧
    (∀ i < n,
      haarBranchSupport (chain (i + 1)) = UnbalancedHaarWavelet.branchSupport (chain i).1 ∨
      haarBranchSupport (chain (i + 1)) = UnbalancedHaarWavelet.branchSupport (chain i).2)

/-- A finite chain inside one fixed refinement tree, starting at that tree's root branch
and moving at each step into one side of the previous branch. -/
def LocalChain_to_Root
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) {level : ℕ} {cell : Set α}
    (hcell : cell ∈ G.grid.partitions level) (n : ℕ)
    (chain : ℕ → (Finset (Set α) × Finset (Set α))) : Prop :=
  chain 0 =
      (H.binaryRefinement.tree level cell hcell).Root ∧
    (∀ i ≤ n, chain i ∈ (H.binaryRefinement.tree level cell hcell).Branches) ∧
    (∀ i < n,
      haarBranchSupport (chain (i + 1)) = UnbalancedHaarWavelet.branchSupport (chain i).1 ∨
      haarBranchSupport (chain (i + 1)) = UnbalancedHaarWavelet.branchSupport (chain i).2)

/-- Every branch in every binary refinement tree is the endpoint of a finite chain
starting at the root of that tree. -/
theorem HaarSystem.exists_LocalChain_to_Root_finish_branch
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} (hcell : cell ∈ G.grid.partitions level)
    {branch : Finset (Set α) × Finset (Set α)}
    (hbranch : branch ∈ (H.binaryRefinement.tree level cell hcell).Branches) :
    ∃ n : ℕ, ∃ chain : ℕ → (Finset (Set α) × Finset (Set α)),
      LocalChain_to_Root G H hcell n chain ∧ chain n = branch := by
  refine ⟨chainLength hbranch, ChainToRoot hbranch, ?_, ?_⟩
  · refine ⟨ChainToRoot_zero hbranch, ?_, ?_⟩
    · intro i hi
      exact ChainToRoot_mem hbranch hi
    · intro i hi
      rcases ChainToRoot_step hbranch hi with hstep | hstep
      · left
        simp [haarBranchSupport, hstep]
      · right
        simp [haarBranchSupport, hstep]
  · exact ChainToRoot_end hbranch

lemma chainLength_eq_of_chainToRoot_eq
    {β : Type*} [DecidableEq β]
    {T : BinaryTreeWithRootandTops β}
    {p q : Finset β × Finset β}
    (hp : p ∈ T.Branches) (hq : q ∈ T.Branches)
    {i : ℕ} (hi : i ≤ chainLength hp)
    (hqi : ChainToRoot hp i = q) :
    i = chainLength hq := by
  exact (ChainToRoot_unique (T := T) hq
    (n := i) (c := ChainToRoot hp)
    (ChainToRoot_zero hp)
    hqi
    (by
      intro j hj
      exact ChainToRoot_mem hp (hj.trans hi))
    (by
      intro j hj
      exact ChainToRoot_step hp (lt_of_lt_of_le hj hi))).1

/-- Inside one refinement tree, two branches at the same local chain length are either
the same branch or have disjoint set-theoretic supports. -/
theorem HaarSystem.haarBranchSupport_same_tree_eq_or_disjoint_of_chainLength_eq
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (n : ℕ) (Q : Set α) (hQ : Q ∈ G.grid.partitions n)
    (p q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches})
    (hlen : chainLength p.2 = chainLength q.2) :
    p = q ∨ Disjoint (haarBranchSupport p.1) (haarBranchSupport q.1) := by
  classical
  by_cases hpq : p = q
  · exact Or.inl hpq
  · right
    let T := H.binaryRefinement.tree n Q hQ
    have hpq_val : p.1 ≠ q.1 := by
      intro h
      exact hpq (Subtype.ext h)
    have hp_childs : p.1.1 ⊆ T.Childs ∧ p.1.2 ⊆ T.Childs :=
      T.TreeStructureChilds p.1 p.2
    have hq_childs : q.1.1 ⊆ T.Childs ∧ q.1.2 ⊆ T.Childs :=
      T.TreeStructureChilds q.1 q.2
    have hp_part : ∀ s, s ∈ Combinatorial_Support p.1 → s ∈ G.grid.partitions (n + 1) := by
      intro s hs
      rcases Finset.mem_union.mp (by simpa [Combinatorial_Support] using hs) with hs1 | hs2
      · exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hp_childs.1 hs1) |>.1
      · exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hp_childs.2 hs2) |>.1
    have hq_part : ∀ s, s ∈ Combinatorial_Support q.1 → s ∈ G.grid.partitions (n + 1) := by
      intro s hs
      rcases Finset.mem_union.mp (by simpa [Combinatorial_Support] using hs) with hs1 | hs2
      · exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.1 hs1) |>.1
      · exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.2 hs2) |>.1
    have hno_sub_pq : ¬ Combinatorial_Support p.1 ⊆ Combinatorial_Support q.1 := by
      intro hsub
      rcases (ChainToRoot_exactly_support_containers p.2 q.2).2 hsub with ⟨i, hi, hqi⟩
      have hi_len : i = chainLength q.2 :=
        chainLength_eq_of_chainToRoot_eq p.2 q.2 hi hqi
      have hi_end : i = chainLength p.2 := by omega
      have hq_eq_p : q.1 = p.1 := by
        have hend := ChainToRoot_end p.2
        rw [hi_end] at hqi
        exact hqi.symm.trans hend
      exact hpq_val hq_eq_p.symm
    have hno_sub_qp : ¬ Combinatorial_Support q.1 ⊆ Combinatorial_Support p.1 := by
      intro hsub
      rcases (ChainToRoot_exactly_support_containers q.2 p.2).2 hsub with ⟨i, hi, hpi⟩
      have hi_len : i = chainLength p.2 :=
        chainLength_eq_of_chainToRoot_eq q.2 p.2 hi hpi
      have hi_end : i = chainLength q.2 := by omega
      have hp_eq_q : p.1 = q.1 := by
        have hend := ChainToRoot_end q.2
        rw [hi_end] at hpi
        exact hpi.symm.trans hend
      exact hpq_val hp_eq_q
    rcases T.SupportProperty p.1 p.2 q.1 q.2 hpq_val with
      hdisj | hp_sub_q1 | hp_sub_q2 | hq_sub_p1 | hq_sub_p2
    · exact haarBranchSupport_disjoint_of_combinatorial_disjoint G hp_part hq_part hdisj
    · exact (hno_sub_pq (hp_sub_q1.trans Finset.subset_union_left)).elim
    · exact (hno_sub_pq (hp_sub_q2.trans Finset.subset_union_right)).elim
    · exact (hno_sub_qp (hq_sub_p1.trans Finset.subset_union_left)).elim
    · exact (hno_sub_qp (hq_sub_p2.trans Finset.subset_union_right)).elim

/-- Laminarity when the first branch is attached to a deeper partition cell than the second.
The deeper support is either contained in one side of the coarser split, hence in the whole
coarser support with different measure, or it is disjoint from the coarser support. -/
theorem HaarSystem.haarBranchSupport_laminar_of_lt_level
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (n m : ℕ) (hnm : n < m)
    (Q : Set α) (hQ : Q ∈ G.grid.partitions n)
    (q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches})
    (P : Set α) (hP : P ∈ G.grid.partitions m)
    (p : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree m P hP).Branches}) :
    (haarBranchSupport p.1 ⊆ haarBranchSupport q.1 ∧
      G.μ (haarBranchSupport p.1) ≠ G.μ (haarBranchSupport q.1)) ∨
    Disjoint (haarBranchSupport p.1) (haarBranchSupport q.1) := by
  classical
  let TP := H.binaryRefinement.tree m P hP
  let TQ := H.binaryRefinement.tree n Q hQ
  have hq_childs : q.1.1 ⊆ TQ.Childs ∧ q.1.2 ⊆ TQ.Childs :=
    TQ.TreeStructureChilds q.1 q.2
  have hq1_part : ∀ s, s ∈ q.1.1 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.1 hs) |>.1
  have hq2_part : ∀ s, s ∈ q.1.2 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hq_childs.2 hs) |>.1
  have hp_sub_P : haarBranchSupport p.1 ⊆ P :=
    H.haarBranchSupport_subset_cell G p
  have hq_sub_Q : haarBranchSupport q.1 ⊆ Q :=
    H.haarBranchSupport_subset_cell G q
  have hPQ_cases : P ⊆ Q ∨ Disjoint P Q :=
    G.partition_subset_or_disjoint_of_le n m hnm.le Q hQ P hP
  rcases hPQ_cases with hPQ_sub | hPQ_disj
  · obtain ⟨c, hc_child, hPc⟩ := G.exists_child_containing_of_lt n m hnm Q hQ P hP hPQ_sub
    have hp_sub_c : haarBranchSupport p.1 ⊆ c := hp_sub_P.trans hPc
    by_cases hc_q1 : c ∈ q.1.1
    · left
      have hsub_side : haarBranchSupport p.1 ⊆ UnbalancedHaarWavelet.branchSupport q.1.1 :=
        hp_sub_c.trans (subset_branchSupport_of_mem hc_q1)
      exact ⟨
        hsub_side.trans (by
          intro x hx
          simpa [haarBranchSupport, branchSupport, Combinatorial_Support] using
            (show x ∈ ⋃ t ∈ ((q.1.1 ∪ q.1.2 : Finset (Set α)) : Set (Set α)), t from by
              rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
              exact Set.mem_iUnion.2
                ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inl hs), hxs⟩⟩)),
        H.measure_ne_of_subset_branchSupport_left G q hsub_side⟩
    · by_cases hc_q2 : c ∈ q.1.2
      · left
        have hsub_side : haarBranchSupport p.1 ⊆ UnbalancedHaarWavelet.branchSupport q.1.2 :=
          hp_sub_c.trans (subset_branchSupport_of_mem hc_q2)
        exact ⟨
          hsub_side.trans (by
            intro x hx
            simpa [haarBranchSupport, branchSupport, Combinatorial_Support] using
              (show x ∈ ⋃ t ∈ ((q.1.1 ∪ q.1.2 : Finset (Set α)) : Set (Set α)), t from by
                rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
                exact Set.mem_iUnion.2
                  ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inr hs), hxs⟩⟩)),
          H.measure_ne_of_subset_branchSupport_right G q hsub_side⟩
      · right
        have hc_q1_disj : Disjoint c (UnbalancedHaarWavelet.branchSupport q.1.1) := by
          refine Set.disjoint_left.2 ?_
          intro x hxc hxq
          rcases (by simpa [branchSupport] using hxq) with ⟨s, hs, hxs⟩
          have hs_ne : s ≠ c := by
            intro hsc
            exact hc_q1 (hsc ▸ hs)
          have hs_disj : Disjoint s c :=
            G.grid.disjoint (n + 1) s c (hq1_part s hs) hc_child.1 hs_ne
          exact (Set.disjoint_left.mp hs_disj hxs hxc).elim
        have hc_q2_disj : Disjoint c (UnbalancedHaarWavelet.branchSupport q.1.2) := by
          refine Set.disjoint_left.2 ?_
          intro x hxc hxq
          rcases (by simpa [branchSupport] using hxq) with ⟨s, hs, hxs⟩
          have hs_ne : s ≠ c := by
            intro hsc
            exact hc_q2 (hsc ▸ hs)
          have hs_disj : Disjoint s c :=
            G.grid.disjoint (n + 1) s c (hq2_part s hs) hc_child.1 hs_ne
          exact (Set.disjoint_left.mp hs_disj hxs hxc).elim
        have hc_q_disj : Disjoint c (haarBranchSupport q.1) := by
          refine Set.disjoint_left.2 ?_
          intro x hxc hxq
          rcases (by simpa [haarBranchSupport, branchSupport, Combinatorial_Support] using hxq)
            with ⟨s, hs, hxs⟩
          rcases hs with hs1 | hs2
          · exact (Set.disjoint_left.mp hc_q1_disj hxc)
              (by
                simpa [branchSupport] using
                  (show x ∈ ⋃ t ∈ (q.1.1 : Set (Set α)), t from
                    Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hs1, hxs⟩⟩))
          · exact (Set.disjoint_left.mp hc_q2_disj hxc)
              (by
                simpa [branchSupport] using
                  (show x ∈ ⋃ t ∈ (q.1.2 : Set (Set α)), t from
                    Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hs2, hxs⟩⟩))
        exact hc_q_disj.mono_left hp_sub_c
  · right
    exact (hPQ_disj.mono_left hp_sub_P).mono_right hq_sub_Q

/-- Globally, among branches of refinement trees, `haarBranchSupport` is injective. -/
theorem HaarSystem.haarBranchSupport_eq_iff_eq_global
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (n m : ℕ)
    (Q P : Set α) (hQ : Q ∈ G.grid.partitions n) (hP : P ∈ G.grid.partitions m)
    (q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches})
    (p : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree m P hP).Branches}) :
    haarBranchSupport q.1 = haarBranchSupport p.1 ↔ q.1 = p.1 := by
  classical
  constructor
  · intro hsupport
    rcases Nat.lt_trichotomy n m with hnm | hnm | hmn
    · rcases H.haarBranchSupport_laminar_of_lt_level G n m hnm Q hQ q P hP p with
        hsub | hdisj
      · rcases hsub with ⟨_hsubset, hmeasure_ne⟩
        exact (hmeasure_ne (by rw [hsupport])).elim
      · have hself_disj : Disjoint (haarBranchSupport q.1) (haarBranchSupport q.1) := by
          simpa [← hsupport] using hdisj.symm
        rcases H.haarBranchSupport_nonempty G n Q hQ q with ⟨x, hx⟩
        exact (Set.disjoint_left.mp hself_disj hx hx).elim
    · subst m
      by_cases hQP : Q = P
      · subst P
        have hproof : hP = hQ := Subsingleton.elim _ _
        subst hP
        exact congrArg Subtype.val
          ((H.haarBranchSupport_eq_iff_eq_same_tree G n Q hQ q p).1 hsupport)
      · have hdisj_QP : Disjoint Q P :=
          G.grid.disjoint n Q P hQ hP hQP
        have hdisj : Disjoint (haarBranchSupport q.1) (haarBranchSupport p.1) :=
          H.haarBranchSupport_disjoint_of_cells_disjoint G q p hdisj_QP
        have hself_disj : Disjoint (haarBranchSupport q.1) (haarBranchSupport q.1) := by
          simpa [← hsupport] using hdisj
        rcases H.haarBranchSupport_nonempty G n Q hQ q with ⟨x, hx⟩
        exact (Set.disjoint_left.mp hself_disj hx hx).elim
    · rcases H.haarBranchSupport_laminar_of_lt_level G m n hmn P hP p Q hQ q with
        hsub | hdisj
      · rcases hsub with ⟨_hsubset, hmeasure_ne⟩
        exact (hmeasure_ne (by rw [← hsupport])).elim
      · have hself_disj : Disjoint (haarBranchSupport q.1) (haarBranchSupport q.1) := by
          simpa [hsupport] using hdisj.symm
        rcases H.haarBranchSupport_nonempty G n Q hQ q with ⟨x, hx⟩
        exact (Set.disjoint_left.mp hself_disj hx hx).elim
  · intro hpq
    rw [hpq]

/-- Support of a globally indexed Haar-system branch. -/
noncomputable def HaarSystem.Index.branchSupport
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) : Set α :=
  haarBranchSupport i.branch.1

lemma HaarSystem.Index.measure_branchSupport_pos
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    0 < G.μ (i.branchSupport G H) := by
  classical
  rcases i with ⟨level, cell, hcell, branch⟩
  let T := H.binaryRefinement.tree level cell hcell
  have hbranch_childs : branch.1.1 ⊆ T.Childs ∧ branch.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds branch.1 branch.2
  have hpart :
      ∀ s, s ∈ Combinatorial_Support branch.1 →
        s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    rcases Finset.mem_union.mp (by simpa [Combinatorial_Support] using hs) with hs1 | hs2
    · exact (H.binaryRefinement.childs_are_children level cell hcell s).1
        (hbranch_childs.1 hs1) |>.1
    · exact (H.binaryRefinement.childs_are_children level cell hcell s).1
        (hbranch_childs.2 hs2) |>.1
  simpa [HaarSystem.Index.branchSupport] using
    measure_haarBranchSupport_pos G branch.2 hpart

/-- The union of all children of a grid cell is the cell itself. -/
lemma HaarSystem.branchSupport_childrenFinset_eq
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (level : ℕ) (cell : Set α) (hcell : cell ∈ G.grid.partitions level) :
    UnbalancedHaarWavelet.branchSupport (G.childrenFinset level cell) = cell := by
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

/-- A cell at level `n+1` has a unique parent cell at level `n`. -/
lemma Grid.parent_unique
    (G : Grid (α := α))
    {n : ℕ} {s parent₁ parent₂ : Set α}
    (hs : s ∈ G.grid.partitions (n + 1))
    (hparent₁ : parent₁ ∈ G.grid.partitions n)
    (hparent₂ : parent₂ ∈ G.grid.partitions n)
    (hs_parent₁ : s ⊆ parent₁)
    (hs_parent₂ : s ⊆ parent₂) :
    parent₁ = parent₂ := by
  by_contra hne
  have hdisj : Disjoint parent₁ parent₂ :=
    G.grid.disjoint n parent₁ parent₂ hparent₁ hparent₂ hne
  obtain ⟨x, hx⟩ := G.partition_nonempty (n + 1) s hs
  exact (Set.disjoint_left.mp hdisj (hs_parent₁ hx) (hs_parent₂ hx)).elim

/-- The support of the root branch of the binary refinement tree of a grid cell is the cell. -/
lemma HaarSystem.haarBranchSupport_root_eq_cell
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level} :
    haarBranchSupport
      (H.binaryRefinement.tree level cell hcell).Root = cell := by
  classical
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
    haarBranchSupport T.Root
        = UnbalancedHaarWavelet.branchSupport (Combinatorial_Support T.Root) := by rfl
    _ = UnbalancedHaarWavelet.branchSupport T.Childs := by rw [hroot_childs]
    _ = UnbalancedHaarWavelet.branchSupport (G.childrenFinset level cell) := by rw [hchilds_finset]
    _ = cell := HaarSystem.branchSupport_childrenFinset_eq G level cell hcell

/-- Every branch in every binary refinement tree is the endpoint of a finite long chain
starting at the root branch of the unique element of the first partition. -/
theorem HaarSystem.exists_LongChain_to_Root_finish_branch
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} (hcell : cell ∈ G.grid.partitions level)
    {branch : Finset (Set α) × Finset (Set α)}
    (hbranch : branch ∈ (H.binaryRefinement.tree level cell hcell).Branches) :
    ∃ n : ℕ, ∃ chain : ℕ → (Finset (Set α) × Finset (Set α)),
      LongChain_to_Root G H n chain ∧ chain n = branch := by
  classical
  induction level generalizing cell branch with
  | zero =>
      have hcell_univ : cell = Set.univ := by
        simpa [G.grid.first_partition_eq_univ] using hcell
      subst cell
      refine ⟨chainLength hbranch, ChainToRoot hbranch, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · simpa using ChainToRoot_zero hbranch
        · intro i hi
          exact ⟨0, Set.univ, hcell, ChainToRoot_mem hbranch hi⟩
        · intro i hi
          rcases ChainToRoot_step hbranch hi with hstep | hstep
          · left
            simp [haarBranchSupport, hstep]
          · right
            simp [haarBranchSupport, hstep]
      · exact ChainToRoot_end hbranch
  | succ level ih =>
      let parent : Set α := Classical.choose (G.grid.nested level cell hcell)
      have hparent : parent ∈ G.grid.partitions level :=
        (Classical.choose_spec (G.grid.nested level cell hcell)).1
      have hcell_parent : cell ⊆ parent :=
        (Classical.choose_spec (G.grid.nested level cell hcell)).2
      let Tparent := H.binaryRefinement.tree level parent hparent
      have hchild : cell ∈ G.children level parent := ⟨hcell, hcell_parent⟩
      have htop : cell ∈ Tparent.Tops :=
        (H.binaryRefinement.tops_are_children level parent hparent cell).2 hchild
      let parentBranch : Finset (Set α) × Finset (Set α) :=
        Classical.choose (Tparent.TopsareTops cell htop)
      have hparentBranch : parentBranch ∈ Tparent.Branches :=
        (Classical.choose_spec (Tparent.TopsareTops cell htop)).1
      have htop_side : ({cell} : Finset (Set α)) ∈ pairToFinset parentBranch :=
        (Classical.choose_spec (Tparent.TopsareTops cell htop)).2
      rcases ih hparent hparentBranch with ⟨n₀, chain₀, hchain₀, hend₀⟩
      let m := chainLength hbranch
      let offset := n₀ + 1
      let chain : ℕ → (Finset (Set α) × Finset (Set α)) :=
        fun k => if h : k ≤ n₀ then chain₀ k else ChainToRoot hbranch (k - offset)
      refine ⟨offset + m, chain, ?_, ?_⟩
      · rcases hchain₀ with ⟨hzero₀, hmem₀, hstep₀⟩
        refine ⟨?_, ?_, ?_⟩
        · have h0le : 0 ≤ n₀ := Nat.zero_le _
          simpa [chain, h0le] using hzero₀
        · intro i hi
          by_cases hi₀ : i ≤ n₀
          · simpa [chain, hi₀] using hmem₀ i hi₀
          · have hlocal_le : i - offset ≤ m := by omega
            refine ⟨level + 1, cell, hcell, ?_⟩
            simpa [chain, hi₀, m] using ChainToRoot_mem hbranch hlocal_le
        · intro i hi
          by_cases hi_lt : i < n₀
          · have hi_le : i ≤ n₀ := Nat.le_of_lt hi_lt
            have his_le : i + 1 ≤ n₀ := Nat.succ_le_of_lt hi_lt
            simpa [chain, hi_le, his_le] using hstep₀ i hi_lt
          · by_cases hi_eq : i = n₀
            · subst i
              have hn_le : n₀ ≤ n₀ := le_rfl
              have hn1_not : ¬ n₀ + 1 ≤ n₀ := Nat.not_succ_le_self n₀
              have hroot_child :
                  haarBranchSupport
                    ((H.binaryRefinement.tree (level + 1) cell hcell).Root)
                    = cell :=
                H.haarBranchSupport_root_eq_cell G
                  (level := level + 1) (cell := cell) (hcell := hcell)
              have hlocal_zero :
                  ChainToRoot hbranch 0 =
                    (H.binaryRefinement.tree (level + 1) cell hcell).Root :=
                ChainToRoot_zero hbranch
              have hside :
                  ({cell} : Finset (Set α)) = parentBranch.1 ∨
                    ({cell} : Finset (Set α)) = parentBranch.2 := by
                dsimp [pairToFinset] at htop_side
                simpa [Finset.mem_insert, Finset.mem_singleton] using htop_side
              have hchain_n : chain₀ n₀ = parentBranch := hend₀
              have hsingleton : UnbalancedHaarWavelet.branchSupport ({cell} : Finset (Set α)) = cell := by
                ext x
                simp [branchSupport]
              rcases hside with hleft | hright
              · left
                calc
                  haarBranchSupport (chain (n₀ + 1))
                      = cell := by
                        simp [chain, offset, hn1_not, hlocal_zero, hroot_child]
                  _ = UnbalancedHaarWavelet.branchSupport (chain n₀).1 := by
                        simp [chain, hchain_n, ← hleft, hsingleton]
              · right
                calc
                  haarBranchSupport (chain (n₀ + 1))
                      = cell := by
                        simp [chain, offset, hn1_not, hlocal_zero, hroot_child]
                  _ = UnbalancedHaarWavelet.branchSupport (chain n₀).2 := by
                        simp [chain, hchain_n, ← hright, hsingleton]
            · have hi_not : ¬ i ≤ n₀ := by omega
              have his_not : ¬ i + 1 ≤ n₀ := by omega
              have hlocal_lt : i - offset < m := by omega
              have hsub_succ : i + 1 - offset = (i - offset) + 1 := by omega
              rcases ChainToRoot_step hbranch hlocal_lt with hstep | hstep
              · left
                simpa [chain, hi_not, his_not, hsub_succ, haarBranchSupport] using
                  congrArg UnbalancedHaarWavelet.branchSupport hstep
              · right
                simpa [chain, hi_not, his_not, hsub_succ, haarBranchSupport] using
                  congrArg UnbalancedHaarWavelet.branchSupport hstep
      · have hnot : ¬ offset + m ≤ n₀ := by omega
        have hsub : offset + m - offset = m := by omega
        simpa [chain, hnot, hsub, m] using ChainToRoot_end hbranch

lemma HaarSystem.chainLength_root
    {β : Type*} [DecidableEq β]
    {T : BinaryTreeWithRootandTops β} :
    chainLength T.RootinBranches = 0 := by
  symm
  exact (ChainToRoot_unique (T := T) T.RootinBranches
    (c := fun _ => T.Root)
    (by rfl)
    (by rfl)
    (by
      intro i hi
      have hi0 : i = 0 := by omega
      simpa [hi0] using T.RootinBranches)
    (by
      intro i hi
      omega)).1









lemma HaarSystem.Index.branchSupport_subset_ambient_cell
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    i.branchSupport G H ⊆ i.cell := by
  rcases i with ⟨level, cell, hcell, branch⟩
  exact H.haarBranchSupport_subset_cell G branch

omit [MeasurableSpace α] in
lemma branchSupport_left_subset_haarBranchSupport [DecidableEq (Set α)]
    (p : Finset (Set α) × Finset (Set α)) :
    UnbalancedHaarWavelet.branchSupport p.1 ⊆ haarBranchSupport p := by
  simpa [haarBranchSupport, Combinatorial_Support] using
    branchSupport_mono (Finset.subset_union_left (s₁ := p.1) (s₂ := p.2))

omit [MeasurableSpace α] in
lemma branchSupport_right_subset_haarBranchSupport [DecidableEq (Set α)]
    (p : Finset (Set α) × Finset (Set α)) :
    UnbalancedHaarWavelet.branchSupport p.2 ⊆ haarBranchSupport p := by
  simpa [haarBranchSupport, Combinatorial_Support] using
    branchSupport_mono (Finset.subset_union_right (s₁ := p.1) (s₂ := p.2))

omit [MeasurableSpace α] in
lemma haarBranchSupport_eq_union_branchSupport [DecidableEq (Set α)]
    (p : Finset (Set α) × Finset (Set α)) :
    haarBranchSupport p = UnbalancedHaarWavelet.branchSupport p.1 ∪ UnbalancedHaarWavelet.branchSupport p.2 := by
  ext x
  constructor
  · intro hx
    rcases (by
      simpa [haarBranchSupport, branchSupport, Combinatorial_Support] using hx) with
      ⟨s, hs, hxs⟩
    rcases hs with hs₁ | hs₂
    · left
      exact by
        simpa [branchSupport] using
          (show x ∈ ⋃ t ∈ (p.1 : Set (Set α)), t from
            Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hs₁, hxs⟩⟩)
    · right
      exact by
        simpa [branchSupport] using
          (show x ∈ ⋃ t ∈ (p.2 : Set (Set α)), t from
            Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨hs₂, hxs⟩⟩)
  · intro hx
    rcases hx with hx₁ | hx₂
    · exact branchSupport_left_subset_haarBranchSupport p hx₁
    · exact branchSupport_right_subset_haarBranchSupport p hx₂

lemma HaarSystem.branchSupport_components_disjoint
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level}
    (p : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree level cell hcell).Branches}) :
    Disjoint (UnbalancedHaarWavelet.branchSupport p.1.1) (UnbalancedHaarWavelet.branchSupport p.1.2) := by
  classical
  let T := H.binaryRefinement.tree level cell hcell
  have hp_childs : p.1.1 ⊆ T.Childs ∧ p.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds p.1 p.2
  have hp1_part : ∀ s, s ∈ p.1.1 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1
      (hp_childs.1 hs) |>.1
  have hp2_part : ∀ s, s ∈ p.1.2 → s ∈ G.grid.partitions (level + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children level cell hcell s).1
      (hp_childs.2 hs) |>.1
  exact disjoint_branchSupport_of_finset_disjoint G level p.1.1 p.1.2
    hp1_part hp2_part (T.DisjointComponents p.1 p.2)

/-- Along a long chain, each next support is contained in the previous support. -/
lemma LongChain_to_Root.support_succ_subset
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) {n : ℕ}
    {chain : ℕ → (Finset (Set α) × Finset (Set α))}
    (hchain : LongChain_to_Root G H n chain)
    {k : ℕ} (hk : k < n) :
    haarBranchSupport (chain (k + 1)) ⊆ haarBranchSupport (chain k) ∧
      haarBranchSupport (chain (k + 1)) ≠ haarBranchSupport (chain k) := by
  rcases hchain with ⟨_hzero, hmem, hstep⟩
  rcases hmem k (Nat.le_of_lt hk) with ⟨level, cell, hcell, hbranch⟩
  rcases hstep k hk with hleft | hright
  · constructor
    · rw [hleft]
      exact branchSupport_left_subset_haarBranchSupport (chain k)
    · intro heq
      have hμ_ne :
          G.μ (UnbalancedHaarWavelet.branchSupport (chain k).1) ≠
            G.μ (haarBranchSupport (chain k)) :=
        H.measure_ne_of_subset_branchSupport_left G
          ({ val := chain k, property := hbranch } :
            {r : Finset (Set α) × Finset (Set α) //
              r ∈ (H.binaryRefinement.tree level cell hcell).Branches})
          Set.Subset.rfl
      exact hμ_ne (by rw [← hleft, heq])
  · constructor
    · rw [hright]
      exact branchSupport_right_subset_haarBranchSupport (chain k)
    · intro heq
      have hμ_ne :
          G.μ (UnbalancedHaarWavelet.branchSupport (chain k).2) ≠
            G.μ (haarBranchSupport (chain k)) :=
        H.measure_ne_of_subset_branchSupport_right G
          ({ val := chain k, property := hbranch } :
            {r : Finset (Set α) × Finset (Set α) //
              r ∈ (H.binaryRefinement.tree level cell hcell).Branches})
          Set.Subset.rfl
      exact hμ_ne (by rw [← hright, heq])

/-- Along a long chain, later supports are contained in earlier supports. -/
lemma LongChain_to_Root.support_mono_le
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) {n : ℕ}
    {chain : ℕ → (Finset (Set α) × Finset (Set α))}
    (hchain : LongChain_to_Root G H n chain)
    {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    haarBranchSupport (chain j) ⊆ haarBranchSupport (chain i) := by
  induction hij with
  | refl =>
      exact Set.Subset.rfl
  | @step k _ hik =>
      have hkn : k ≤ n := le_trans (Nat.le_succ k) hjn
      have hsucc : haarBranchSupport (chain (k + 1)) ⊆ haarBranchSupport (chain k) :=
        (hchain.support_succ_subset G H (Nat.lt_of_succ_le hjn)).1
      exact hsucc.trans (hik hkn)

/-- Along a long chain, a strictly later support is properly contained in the earlier support. -/
lemma LongChain_to_Root.support_mono
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) {n : ℕ}
    {chain : ℕ → (Finset (Set α) × Finset (Set α))}
    (hchain : LongChain_to_Root G H n chain)
    {i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
    haarBranchSupport (chain j) ⊆ haarBranchSupport (chain i) ∧
      haarBranchSupport (chain j) ≠ haarBranchSupport (chain i) := by
  constructor
  · exact hchain.support_mono_le G H hij.le hjn
  · intro heq
    have hi_succ_le_j : i + 1 ≤ j := Nat.succ_le_of_lt hij
    have hi_lt_n : i < n := Nat.lt_of_succ_le (hi_succ_le_j.trans hjn)
    have hsucc := hchain.support_succ_subset G H hi_lt_n
    have htail :
        haarBranchSupport (chain j) ⊆ haarBranchSupport (chain (i + 1)) :=
      hchain.support_mono_le G H hi_succ_le_j hjn
    have hreverse :
        haarBranchSupport (chain i) ⊆ haarBranchSupport (chain (i + 1)) := by
      simpa [heq] using htail
    have heq_succ :
        haarBranchSupport (chain (i + 1)) = haarBranchSupport (chain i) :=
      Set.Subset.antisymm hsucc.1 hreverse
    exact hsucc.2 heq_succ

/-- The final support of a long chain is nonempty. -/
lemma LongChain_to_Root.final_support_nonempty
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) {n : ℕ}
    {chain : ℕ → (Finset (Set α) × Finset (Set α))}
    (hchain : LongChain_to_Root G H n chain) :
    (haarBranchSupport (chain n)).Nonempty := by
  classical
  rcases hchain with ⟨_hzero, hmem, _hstep⟩
  rcases hmem n le_rfl with ⟨level, cell, hcell, hbranch⟩
  let T := H.binaryRefinement.tree level cell hcell
  obtain ⟨s, hs⟩ := (T.NonemptyPairs (chain n) hbranch).1
  have hs_child : s ∈ T.Childs :=
    (T.TreeStructureChilds (chain n) hbranch).1 hs
  have hs_part : s ∈ G.grid.partitions (level + 1) :=
    ((H.binaryRefinement.childs_are_children level cell hcell s).1 hs_child).1
  obtain ⟨x, hx⟩ := G.partition_nonempty (level + 1) s hs_part
  exact ⟨x, by
    rw [haarBranchSupport, branchSupport, Combinatorial_Support]
    exact Set.mem_iUnion.2
      ⟨s, Set.mem_iUnion.2 ⟨Finset.mem_union_left (chain n).2 hs, hx⟩⟩⟩

/-- If two long chains split from the same branch by taking opposite sides, then their final
branch supports are disjoint. -/
theorem LongChain_to_Root.disjoint_final_of_split_left_right
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {m n i : ℕ}
    {chain₁ chain₂ : ℕ → (Finset (Set α) × Finset (Set α))}
    (hchain₁ : LongChain_to_Root G H m chain₁)
    (hchain₂ : LongChain_to_Root G H n chain₂)
    (hi_pos : 0 < i) (him : i ≤ m) (hin : i ≤ n)
    (hprev : chain₁ (i - 1) = chain₂ (i - 1))
    (hleft :
      haarBranchSupport (chain₁ i) = UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).1)
    (hright :
      haarBranchSupport (chain₂ i) = UnbalancedHaarWavelet.branchSupport (chain₂ (i - 1)).2) :
    Disjoint (haarBranchSupport (chain₁ m)) (haarBranchSupport (chain₂ n)) := by
  classical
  rcases hchain₁ with ⟨hzero₁, hmem₁, hstep₁⟩
  have hchain₁' : LongChain_to_Root G H m chain₁ := ⟨hzero₁, hmem₁, hstep₁⟩
  have hchain₂' : LongChain_to_Root G H n chain₂ := hchain₂
  rcases hmem₁ (i - 1) (by omega) with ⟨level, cell, hcell, hbranch_prev⟩
  have hside_disj :
      Disjoint (UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).1)
        (UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).2) := by
    simpa using
      H.branchSupport_components_disjoint G
        ({ val := chain₁ (i - 1), property := hbranch_prev } :
          {r : Finset (Set α) × Finset (Set α) //
            r ∈ (H.binaryRefinement.tree level cell hcell).Branches})
  have hdisj_i :
      Disjoint (haarBranchSupport (chain₁ i)) (haarBranchSupport (chain₂ i)) := by
    rw [hleft, hright, ← hprev]
    exact hside_disj
  have hsub₁ :
      haarBranchSupport (chain₁ m) ⊆ haarBranchSupport (chain₁ i) :=
    hchain₁'.support_mono_le G H him le_rfl
  have hsub₂ :
      haarBranchSupport (chain₂ n) ⊆ haarBranchSupport (chain₂ i) :=
    hchain₂'.support_mono_le G H hin le_rfl
  exact (hdisj_i.mono_left hsub₁).mono_right hsub₂

/-- Symmetric version: the first chain takes the right side and the second takes the left side. -/
theorem LongChain_to_Root.disjoint_final_of_split_right_left
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {m n i : ℕ}
    {chain₁ chain₂ : ℕ → (Finset (Set α) × Finset (Set α))}
    (hchain₁ : LongChain_to_Root G H m chain₁)
    (hchain₂ : LongChain_to_Root G H n chain₂)
    (hi_pos : 0 < i) (him : i ≤ m) (hin : i ≤ n)
    (hprev : chain₁ (i - 1) = chain₂ (i - 1))
    (hright :
      haarBranchSupport (chain₁ i) = UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).2)
    (hleft :
      haarBranchSupport (chain₂ i) = UnbalancedHaarWavelet.branchSupport (chain₂ (i - 1)).1) :
    Disjoint (haarBranchSupport (chain₁ m)) (haarBranchSupport (chain₂ n)) := by
  classical
  have hdisj :=
    LongChain_to_Root.disjoint_final_of_split_left_right
      G H hchain₂ hchain₁ hi_pos hin him hprev.symm hleft (by simpa [hprev] using hright)
  exact hdisj.symm

/-- If two long chains with the same endpoint have no split before `min m n`, then they agree
up to `min m n`. -/
lemma LongChain_to_Root.eq_on_common_prefix_of_no_split
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {m n : ℕ}
    {chain₁ chain₂ : ℕ → (Finset (Set α) × Finset (Set α))}
    (hchain₁ : LongChain_to_Root G H m chain₁)
    (hchain₂ : LongChain_to_Root G H n chain₂)
    (hno_split :
      ∀ i, 0 < i → i ≤ m → i ≤ n →
        chain₁ (i - 1) = chain₂ (i - 1) → chain₁ i = chain₂ i)
    {i : ℕ} (him : i ≤ m) (hin : i ≤ n) :
    chain₁ i = chain₂ i := by
  induction i with
  | zero =>
      rcases hchain₁ with ⟨hzero₁, _hmem₁, _hstep₁⟩
      rcases hchain₂ with ⟨hzero₂, _hmem₂, _hstep₂⟩
      exact hzero₁.trans hzero₂.symm
  | succ i ih =>
      have hprev : chain₁ (i + 1 - 1) = chain₂ (i + 1 - 1) := by
        simpa using ih (by omega) (by omega)
      exact hno_split (i + 1) (by omega) him hin hprev

/-- Uniqueness of a long chain ending at a fixed branch. -/
theorem LongChain_to_Root.unique_of_same_final
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {m n : ℕ}
    {chain₁ chain₂ : ℕ → (Finset (Set α) × Finset (Set α))}
    (hchain₁ : LongChain_to_Root G H m chain₁)
    (hchain₂ : LongChain_to_Root G H n chain₂)
    (hend : chain₁ m = chain₂ n) :
    m = n ∧ ∀ i ≤ m, chain₁ i = chain₂ i := by
  classical
  have hmem₁ := hchain₁.2.1
  have hstep₁ := hchain₁.2.2
  have hmem₂ := hchain₂.2.1
  have hstep₂ := hchain₂.2.2
  have hfinal_support :
      haarBranchSupport (chain₁ m) = haarBranchSupport (chain₂ n) := by
    rw [hend]
  have hno_split :
      ∀ i, 0 < i → i ≤ m → i ≤ n →
        chain₁ (i - 1) = chain₂ (i - 1) → chain₁ i = chain₂ i := by
    intro i hi_pos him hin hprev
    by_contra hne
    have hk₁ : i - 1 < m := by omega
    have hk₂ : i - 1 < n := by omega
    have hsucc : i - 1 + 1 = i := Nat.sub_add_cancel hi_pos
    have hstep_i₁ := hstep₁ (i - 1) hk₁
    have hstep_i₂ := hstep₂ (i - 1) hk₂
    rcases hstep_i₁ with hleft₁ | hright₁ <;> rcases hstep_i₂ with hleft₂ | hright₂
    · have hleft₁' :
          haarBranchSupport (chain₁ i) = UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).1 := by
        simpa [hsucc] using hleft₁
      have hleft₂' :
          haarBranchSupport (chain₂ i) = UnbalancedHaarWavelet.branchSupport (chain₂ (i - 1)).1 := by
        simpa [hsucc] using hleft₂
      have hsupport_eq :
          haarBranchSupport (chain₁ i) = haarBranchSupport (chain₂ i) := by
        rw [hleft₁', hleft₂', hprev]
      rcases hmem₁ i him with ⟨level₁, cell₁, hcell₁, hbranch₁⟩
      rcases hmem₂ i hin with ⟨level₂, cell₂, hcell₂, hbranch₂⟩
      exact hne
        ((H.haarBranchSupport_eq_iff_eq_global G level₁ level₂ cell₁ cell₂
          hcell₁ hcell₂ ⟨chain₁ i, hbranch₁⟩ ⟨chain₂ i, hbranch₂⟩).1 hsupport_eq)
    · have hleft :
          haarBranchSupport (chain₁ i) = UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).1 := by
        simpa [hsucc] using hleft₁
      have hright :
          haarBranchSupport (chain₂ i) = UnbalancedHaarWavelet.branchSupport (chain₂ (i - 1)).2 := by
        simpa [hsucc] using hright₂
      have hdisj :=
        LongChain_to_Root.disjoint_final_of_split_left_right
          G H hchain₁ hchain₂ hi_pos him hin hprev hleft hright
      have hnonempty :
          (haarBranchSupport (chain₂ n)).Nonempty :=
        hchain₂.final_support_nonempty G H
      rcases hnonempty with ⟨x, hx⟩
      exact (Set.disjoint_left.mp hdisj (by simpa [hfinal_support] using hx) hx).elim
    · have hright :
          haarBranchSupport (chain₁ i) = UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).2 := by
        simpa [hsucc] using hright₁
      have hleft :
          haarBranchSupport (chain₂ i) = UnbalancedHaarWavelet.branchSupport (chain₂ (i - 1)).1 := by
        simpa [hsucc] using hleft₂
      have hdisj :=
        LongChain_to_Root.disjoint_final_of_split_right_left
          G H hchain₁ hchain₂ hi_pos him hin hprev hright hleft
      have hnonempty :
          (haarBranchSupport (chain₂ n)).Nonempty :=
        hchain₂.final_support_nonempty G H
      rcases hnonempty with ⟨x, hx⟩
      exact (Set.disjoint_left.mp hdisj (by simpa [hfinal_support] using hx) hx).elim
    · have hright₁' :
          haarBranchSupport (chain₁ i) = UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).2 := by
        simpa [hsucc] using hright₁
      have hright₂' :
          haarBranchSupport (chain₂ i) = UnbalancedHaarWavelet.branchSupport (chain₂ (i - 1)).2 := by
        simpa [hsucc] using hright₂
      have hsupport_eq :
          haarBranchSupport (chain₁ i) = haarBranchSupport (chain₂ i) := by
        rw [hright₁', hright₂', hprev]
      rcases hmem₁ i him with ⟨level₁, cell₁, hcell₁, hbranch₁⟩
      rcases hmem₂ i hin with ⟨level₂, cell₂, hcell₂, hbranch₂⟩
      exact hne
        ((H.haarBranchSupport_eq_iff_eq_global G level₁ level₂ cell₁ cell₂
          hcell₁ hcell₂ ⟨chain₁ i, hbranch₁⟩ ⟨chain₂ i, hbranch₂⟩).1 hsupport_eq)
  have hprefix :
      ∀ i, i ≤ m → i ≤ n → chain₁ i = chain₂ i := by
    intro i him hin
    exact LongChain_to_Root.eq_on_common_prefix_of_no_split
      G H hchain₁ hchain₂ hno_split him hin
  have hmn : m = n := by
    by_cases hle : m ≤ n
    · by_contra hne
      have hlt : m < n := lt_of_le_of_ne hle hne
      have hsub_ne := hchain₂.support_mono G H hlt le_rfl
      have h_eq_m : chain₁ m = chain₂ m := hprefix m le_rfl hle
      exact hsub_ne.2 (by
        rw [← hfinal_support]
        simpa [h_eq_m])
    · have hlt : n < m := by omega
      have hsub_ne := hchain₁.support_mono G H hlt le_rfl
      have h_eq_n : chain₁ n = chain₂ n := hprefix n (Nat.le_of_lt hlt) le_rfl
      exfalso
      exact (hsub_ne.2 (by
        rw [hfinal_support]
        simpa [h_eq_n]))
  subst n
  exact ⟨rfl, by
    intro i hi
    exact hprefix i hi hi⟩

/-- Two long chains with the same length end either at the same support or at disjoint
supports. -/
theorem LongChain_to_Root.eq_or_disjoint_final_of_same_length
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {n : ℕ}
    {chain₁ chain₂ : ℕ → (Finset (Set α) × Finset (Set α))}
    (hchain₁ : LongChain_to_Root G H n chain₁)
    (hchain₂ : LongChain_to_Root G H n chain₂) :
    haarBranchSupport (chain₁ n) = haarBranchSupport (chain₂ n) ∨
      Disjoint (haarBranchSupport (chain₁ n)) (haarBranchSupport (chain₂ n)) := by
  classical
  have hmem₁ := hchain₁.2.1
  have hstep₁ := hchain₁.2.2
  have hmem₂ := hchain₂.2.1
  have hstep₂ := hchain₂.2.2
  by_cases hno_split :
      ∀ i, 0 < i → i ≤ n →
        chain₁ (i - 1) = chain₂ (i - 1) → chain₁ i = chain₂ i
  · left
    have hprefix :
        ∀ i, i ≤ n → chain₁ i = chain₂ i := by
      intro i hin
      exact LongChain_to_Root.eq_on_common_prefix_of_no_split
        G H hchain₁ hchain₂
        (by
          intro k hkpos hkm hkn hprev
          exact hno_split k hkpos hkm hprev)
        hin hin
    rw [hprefix n le_rfl]
  · push_neg at hno_split
    rcases hno_split with ⟨i, hi_pos, hin, hprev, hne⟩
    right
    have hk : i - 1 < n := by omega
    have hsucc : i - 1 + 1 = i := Nat.sub_add_cancel hi_pos
    have hstep_i₁ := hstep₁ (i - 1) hk
    have hstep_i₂ := hstep₂ (i - 1) hk
    rcases hstep_i₁ with hleft₁ | hright₁ <;> rcases hstep_i₂ with hleft₂ | hright₂
    · have hleft₁' :
          haarBranchSupport (chain₁ i) =
            UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).1 := by
        simpa [hsucc] using hleft₁
      have hleft₂' :
          haarBranchSupport (chain₂ i) =
            UnbalancedHaarWavelet.branchSupport (chain₂ (i - 1)).1 := by
        simpa [hsucc] using hleft₂
      have hsupport_eq :
          haarBranchSupport (chain₁ i) = haarBranchSupport (chain₂ i) := by
        rw [hleft₁', hleft₂', hprev]
      rcases hmem₁ i hin with ⟨level₁, cell₁, hcell₁, hbranch₁⟩
      rcases hmem₂ i hin with ⟨level₂, cell₂, hcell₂, hbranch₂⟩
      exact (hne
        ((H.haarBranchSupport_eq_iff_eq_global G level₁ level₂ cell₁ cell₂
          hcell₁ hcell₂ ⟨chain₁ i, hbranch₁⟩ ⟨chain₂ i, hbranch₂⟩).1 hsupport_eq)).elim
    · have hleft :
          haarBranchSupport (chain₁ i) =
            UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).1 := by
        simpa [hsucc] using hleft₁
      have hright :
          haarBranchSupport (chain₂ i) =
            UnbalancedHaarWavelet.branchSupport (chain₂ (i - 1)).2 := by
        simpa [hsucc] using hright₂
      exact LongChain_to_Root.disjoint_final_of_split_left_right
        G H hchain₁ hchain₂ hi_pos hin hin hprev hleft hright
    · have hright :
          haarBranchSupport (chain₁ i) =
            UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).2 := by
        simpa [hsucc] using hright₁
      have hleft :
          haarBranchSupport (chain₂ i) =
            UnbalancedHaarWavelet.branchSupport (chain₂ (i - 1)).1 := by
        simpa [hsucc] using hleft₂
      exact LongChain_to_Root.disjoint_final_of_split_right_left
        G H hchain₁ hchain₂ hi_pos hin hin hprev hright hleft
    · have hright₁' :
          haarBranchSupport (chain₁ i) =
            UnbalancedHaarWavelet.branchSupport (chain₁ (i - 1)).2 := by
        simpa [hsucc] using hright₁
      have hright₂' :
          haarBranchSupport (chain₂ i) =
            UnbalancedHaarWavelet.branchSupport (chain₂ (i - 1)).2 := by
        simpa [hsucc] using hright₂
      have hsupport_eq :
          haarBranchSupport (chain₁ i) = haarBranchSupport (chain₂ i) := by
        rw [hright₁', hright₂', hprev]
      rcases hmem₁ i hin with ⟨level₁, cell₁, hcell₁, hbranch₁⟩
      rcases hmem₂ i hin with ⟨level₂, cell₂, hcell₂, hbranch₂⟩
      exact (hne
        ((H.haarBranchSupport_eq_iff_eq_global G level₁ level₂ cell₁ cell₂
          hcell₁ hcell₂ ⟨chain₁ i, hbranch₁⟩ ⟨chain₂ i, hbranch₂⟩).1 hsupport_eq)).elim

/-- Append one branch to a long chain, provided its support is one side of the previous
endpoint. -/
lemma LongChain_to_Root.extend_one
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {n : ℕ} {chain : ℕ → (Finset (Set α) × Finset (Set α))}
    (hchain : LongChain_to_Root G H n chain)
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level}
    {q : Finset (Set α) × Finset (Set α)}
    (hq : q ∈ (H.binaryRefinement.tree level cell hcell).Branches)
    (hstep :
      haarBranchSupport q = UnbalancedHaarWavelet.branchSupport (chain n).1 ∨
      haarBranchSupport q = UnbalancedHaarWavelet.branchSupport (chain n).2) :
    LongChain_to_Root G H (n + 1) (fun k => if h : k ≤ n then chain k else q) ∧
      (fun k => if h : k ≤ n then chain k else q) (n + 1) = q := by
  classical
  rcases hchain with ⟨hzero, hmem, hsteps⟩
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · have h0 : 0 ≤ n := Nat.zero_le _
      simpa [h0] using hzero
    · intro i hi
      by_cases hin : i ≤ n
      · simpa [hin] using hmem i hin
      · have hi_last : i = n + 1 := by omega
        refine ⟨level, cell, hcell, ?_⟩
        simpa [hi_last, hin] using hq
    · intro i hi
      by_cases hin_lt : i < n
      · have hi_le : i ≤ n := Nat.le_of_lt hin_lt
        have his_le : i + 1 ≤ n := Nat.succ_le_of_lt hin_lt
        simpa [hi_le, his_le] using hsteps i hin_lt
      · have hi_eq : i = n := by omega
        subst i
        have hn_le : n ≤ n := le_rfl
        have hns_not : ¬ n + 1 ≤ n := Nat.not_succ_le_self n
        simpa [hn_le, hns_not] using hstep
  · have hnot : ¬ n + 1 ≤ n := Nat.not_succ_le_self n
    simp [hnot]


/-- The deepness of a globally indexed Haar branch.

It is the length of the unique long chain, starting at the global root branch, whose endpoint
is the indexed branch. -/
noncomputable def HaarSystem.Index.deepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) : ℕ :=
  Classical.choose
    (H.exists_LongChain_to_Root_finish_branch G i.hcell i.branch.2)


@[simp]
lemma HaarSystem.Index.deepness_mk
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (level : ℕ) (cell : Set α) (hcell : cell ∈ G.grid.partitions level)
    (branch : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree level cell hcell).Branches}) :
    (HaarSystem.Index.deepness G H
      ({ level := level, cell := cell, hcell := hcell, branch := branch } : H.Index))
      =
        Classical.choose
          (H.exists_LongChain_to_Root_finish_branch G hcell branch.2) := by
  rfl

/-- The chosen deepness is characterized by any long chain ending at the indexed branch. -/
lemma HaarSystem.Index.deepness_eq_of_LongChain_to_Root
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index)
    {n : ℕ} {chain : ℕ → (Finset (Set α) × Finset (Set α))}
    (hchain : LongChain_to_Root G H n chain)
    (hend : chain n = i.branch.1) :
    i.deepness G H = n := by
  classical
  let h_exists := H.exists_LongChain_to_Root_finish_branch G i.hcell i.branch.2
  let n₀ := Classical.choose h_exists
  let chain₀ := Classical.choose (Classical.choose_spec h_exists)
  have hchosen :
      LongChain_to_Root G H n₀ chain₀ ∧ chain₀ n₀ = i.branch.1 :=
    Classical.choose_spec (Classical.choose_spec h_exists)
  have huniq :=
    LongChain_to_Root.unique_of_same_final G H hchosen.1 hchain
      (by rw [hchosen.2, hend])
  exact huniq.1

lemma HaarSystem.Index.deepness_eq_succ_of_haarBranchSupport_eq_side
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i j : H.Index)
    (hstep :
      haarBranchSupport j.branch.1 = UnbalancedHaarWavelet.branchSupport i.branch.1.1 ∨
      haarBranchSupport j.branch.1 = UnbalancedHaarWavelet.branchSupport i.branch.1.2) :
    j.deepness G H = i.deepness G H + 1 := by
  classical
  let h_exists := H.exists_LongChain_to_Root_finish_branch G i.hcell i.branch.2
  let chain := Classical.choose (Classical.choose_spec h_exists)
  have hchain :
      LongChain_to_Root G H (i.deepness G H) chain ∧
        chain (i.deepness G H) = i.branch.1 := by
    simpa [HaarSystem.Index.deepness, h_exists, chain] using
      (Classical.choose_spec (Classical.choose_spec h_exists))
  have hstep' :
      haarBranchSupport j.branch.1 = UnbalancedHaarWavelet.branchSupport (chain (i.deepness G H)).1 ∨
      haarBranchSupport j.branch.1 = UnbalancedHaarWavelet.branchSupport (chain (i.deepness G H)).2 := by
    simpa [hchain.2] using hstep
  let chain' : ℕ → (Finset (Set α) × Finset (Set α)) :=
    fun k => if h : k ≤ i.deepness G H then chain k else j.branch.1
  have hext :
      LongChain_to_Root G H (i.deepness G H + 1) chain' ∧
        chain' (i.deepness G H + 1) = j.branch.1 := by
    simpa [chain'] using
      LongChain_to_Root.extend_one G H hchain.1 j.branch.2 hstep'
  exact j.deepness_eq_of_LongChain_to_Root G H hext.1 hext.2

omit [MeasurableSpace α] in
lemma branchSupport_singleton [DecidableEq (Set α)] (s : Set α) :
    UnbalancedHaarWavelet.branchSupport ({s} : Finset (Set α)) = s := by
  ext x
  simp [branchSupport]

lemma HaarSystem.Index.branchSupport_eq_cell_of_chainLength_zero
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index)
    (hzero : chainLength i.branch.2 = 0) :
    i.branchSupport G H = i.cell := by
  classical
  rcases i with ⟨level, cell, hcell, branch⟩
  let T := H.binaryRefinement.tree level cell hcell
  have hbranch_root : branch.1 = T.Root := by
    have hroot := ChainToRoot_zero branch.2
    have hend := ChainToRoot_end branch.2
    rw [hzero] at hend
    exact hend.symm.trans hroot
  dsimp [HaarSystem.Index.branchSupport]
  simpa [T, hbranch_root] using
    (H.haarBranchSupport_root_eq_cell G
      (level := level) (cell := cell) (hcell := hcell))

lemma HaarSystem.Index.exists_parent_branchSupport_of_chainLength_pos
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index)
    (hpos : 0 < chainLength i.branch.2) :
    ∃ j : H.Index,
      j.deepness G H + 1 = i.deepness G H ∧
      i.branchSupport G H ⊆ j.branchSupport G H := by
  classical
  rcases i with ⟨level, cell, hcell, branch⟩
  let T := H.binaryRefinement.tree level cell hcell
  let parentBranch : Finset (Set α) × Finset (Set α) :=
    ChainToRoot branch.2 (chainLength branch.2 - 1)
  have hparent_le : chainLength branch.2 - 1 ≤ chainLength branch.2 := by omega
  have hparent_mem : parentBranch ∈ T.Branches :=
    ChainToRoot_mem branch.2 hparent_le
  let parentIndex : H.Index :=
    { level := level
      cell := cell
      hcell := hcell
      branch := ⟨parentBranch, hparent_mem⟩ }
  refine ⟨parentIndex, ?_, ?_⟩
  · have hpred : chainLength branch.2 - 1 + 1 = chainLength branch.2 :=
      Nat.succ_pred_eq_of_pos hpos
    have hlocal_step :=
      ChainToRoot_step branch.2 (i := chainLength branch.2 - 1) (by omega)
    have hside :
        haarBranchSupport branch.1 =
            UnbalancedHaarWavelet.branchSupport parentBranch.1 ∨
          haarBranchSupport branch.1 =
            UnbalancedHaarWavelet.branchSupport parentBranch.2 := by
      rw [hpred, ChainToRoot_end branch.2] at hlocal_step
      rcases hlocal_step with hleft | hright
      · left
        simpa [parentBranch, haarBranchSupport] using
          congrArg UnbalancedHaarWavelet.branchSupport hleft
      · right
        simpa [parentBranch, haarBranchSupport] using
          congrArg UnbalancedHaarWavelet.branchSupport hright
    let currentIndex : H.Index :=
      { level := level
        cell := cell
        hcell := hcell
        branch := branch }
    have hdeep :=
      HaarSystem.Index.deepness_eq_succ_of_haarBranchSupport_eq_side
        G H parentIndex currentIndex hside
    simpa [parentIndex, currentIndex] using hdeep.symm
  · have hsub_combinatorial :
        Combinatorial_Support branch.1 ⊆ Combinatorial_Support parentBranch := by
      have hend : ChainToRoot branch.2 (chainLength branch.2) = branch.1 :=
        ChainToRoot_end branch.2
      have hstep := chain_endpoint_support_subset
        (T := T) (p := branch.1)
        (n := chainLength branch.2)
        (c := ChainToRoot branch.2)
        hend
        (by
          intro k hk
          exact ChainToRoot_step branch.2 hk)
        (chainLength branch.2 - 1)
        (by omega)
      simpa [parentBranch] using hstep
    exact haarBranchSupport_subset_of_combinatorial_subset hsub_combinatorial

/-- The global index corresponding to the root branch over the unique level-zero cell. -/
noncomputable def HaarSystem.rootIndex
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) : H.Index :=
  let hrootCell : (Set.univ : Set α) ∈ G.grid.partitions 0 := by
    simpa [G.grid.first_partition_eq_univ]
  let T := H.binaryRefinement.tree 0 (Set.univ : Set α) hrootCell
  { level := 0
    cell := Set.univ
    hcell := hrootCell
    branch := ⟨T.Root, T.RootinBranches⟩ }

@[simp]
lemma HaarSystem.rootIndex_branchSupport
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    (H.rootIndex G).branchSupport G H = Set.univ := by
  classical
  dsimp [HaarSystem.rootIndex, HaarSystem.Index.branchSupport]
  simpa using
    (H.haarBranchSupport_root_eq_cell G
      (level := 0) (cell := (Set.univ : Set α)))

@[simp]
lemma HaarSystem.rootIndex_deepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    (H.rootIndex G).deepness G H = 0 := by
  classical
  let chain : ℕ → (Finset (Set α) × Finset (Set α)) :=
    fun _ =>
      (H.binaryRefinement.tree 0 (Set.univ : Set α)
        (by simp [G.grid.first_partition_eq_univ])).Root
  have hchain : LongChain_to_Root G H 0 chain := by
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · intro i hi
      have hi0 : i = 0 := by omega
      refine ⟨0, Set.univ, by simp [G.grid.first_partition_eq_univ], ?_⟩
      simpa [chain, hi0] using
        (H.binaryRefinement.tree 0 (Set.univ : Set α)
          (by simp [G.grid.first_partition_eq_univ])).RootinBranches
    · intro i hi
      omega
  have hend : chain 0 = (H.rootIndex G).branch.1 := by
    rfl
  exact (H.rootIndex G).deepness_eq_of_LongChain_to_Root G H hchain hend


/-- The set of all supports of branches of a Haar system. -/
noncomputable def HaarSystem.branchSupports
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) : Set (Set α) :=
  Set.range (fun i : H.Index => i.branchSupport G H)

/-- The supports of all Haar branches whose induced binary-grid deepness is `n`. -/
noncomputable def HaarSystem.supportsAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n : ℕ) : Set (Set α) :=
  {S | ∃ i : H.Index, i.branchSupport G H = S ∧ i.deepness G H = n}

lemma HaarSystem.mem_supportsAtDeepness_iff
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n : ℕ) (S : Set α) :
    S ∈ H.supportsAtDeepness G n ↔
      ∃ i : H.Index, i.branchSupport G H = S ∧ i.deepness G H = n := by
  rfl

lemma HaarSystem.measure_pos_of_mem_supportsAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) {n : ℕ} {S : Set α}
    (hS : S ∈ H.supportsAtDeepness G n) :
    0 < G.μ S := by
  rcases hS with ⟨i, rfl, _hi⟩
  exact i.measure_branchSupport_pos G H

/-- The nodes of the binary grid induced by a Haar system at deepness `n`.

With the current definition of `Index.deepness`, these are exactly the supports of the
globally indexed Haar branches whose unique long chain from the root has length `n`. -/
noncomputable def HaarSystem.nodesAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n : ℕ) : Set (Set α) :=
  {S | ∃ i : H.Index, i.branchSupport G H = S ∧ i.deepness G H = n}

lemma HaarSystem.mem_nodesAtDeepness_iff
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n : ℕ) (S : Set α) :
    S ∈ H.nodesAtDeepness G n ↔
      ∃ i : H.Index, i.branchSupport G H = S ∧ i.deepness G H = n := by
  rfl

lemma HaarSystem.branchSupport_mem_nodesAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    i.branchSupport G H ∈ H.nodesAtDeepness G (i.deepness G H) := by
  exact ⟨i, rfl, rfl⟩

lemma HaarSystem.nodesAtDeepness_eq_supportsAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n : ℕ) :
    H.nodesAtDeepness G n = H.supportsAtDeepness G n := by
  rfl

lemma HaarSystem.measure_pos_of_mem_nodesAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) {n : ℕ} {S : Set α}
    (hS : S ∈ H.nodesAtDeepness G n) :
    0 < G.μ S := by
  rcases hS with ⟨i, rfl, _hi⟩
  exact i.measure_branchSupport_pos G H









/-- General laminarity of supports of two globally indexed Haar branches.

For any two branches in a Haar system, either they are the same global index, or one
support is contained in the other and the two measures differ, or the supports are disjoint. -/
theorem HaarSystem.haarBranchSupport_laminar_indices
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i j : H.Index) :
    i = j ∨
      (i.branchSupport G H ⊆ j.branchSupport G H ∧
        G.μ (i.branchSupport G H) ≠ G.μ (j.branchSupport G H)) ∨
      (j.branchSupport G H ⊆ i.branchSupport G H ∧
        G.μ (j.branchSupport G H) ≠ G.μ (i.branchSupport G H)) ∨
      Disjoint (i.branchSupport G H) (j.branchSupport G H) := by
  classical
  rcases i with ⟨n, Q, hQ, q⟩
  rcases j with ⟨m, P, hP, p⟩
  dsimp [HaarSystem.Index.branchSupport]
  rcases Nat.lt_trichotomy n m with hnm | hnm | hmn
  · right
    rcases H.haarBranchSupport_laminar_of_lt_level G n m hnm Q hQ q P hP p with hsub | hdisj
    · right
      left
      exact hsub
    · right
      right
      exact hdisj.symm
  · subst m
    by_cases hQP : Q = P
    · subst P
      have hproof : hP = hQ := Subsingleton.elim _ _
      subst hP
      rcases H.haarBranchSupport_laminar_same_tree G n Q hQ q p with hqp | hsub | hsub | hdisj
      · subst p
        exact Or.inl rfl
      · exact Or.inr (Or.inl hsub)
      · exact Or.inr (Or.inr (Or.inl hsub))
      · exact Or.inr (Or.inr (Or.inr hdisj))
    · right
      right
      right
      have hdisj_QP : Disjoint Q P :=
        G.grid.disjoint n Q P hQ hP hQP
      exact H.haarBranchSupport_disjoint_of_cells_disjoint G q p hdisj_QP
  · right
    rcases H.haarBranchSupport_laminar_of_lt_level G m n hmn P hP p Q hQ q with hsub | hdisj
    · left
      exact hsub
    · right
      right
      exact hdisj




end UnbalancedHaarWavelet

namespace UnbalancedHaarWavelet

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
lemma chainLength_eq_succ_of_support_eq_left
    [DecidableEq (Set α)]
    {T : BinaryTreeWithRootandTops (Set α)}
    {p q : Finset (Set α) × Finset (Set α)}
    (hp : p ∈ T.Branches) (hq : q ∈ T.Branches)
    (hqp : Combinatorial_Support q = p.1) :
    chainLength hq = chainLength hp + 1 := by
  let c : ℕ → Finset (Set α) × Finset (Set α) :=
    fun k => if h : k ≤ chainLength hp then ChainToRoot hp k else q
  have hc0 : c 0 = T.Root := by
    have h0 : 0 ≤ chainLength hp := Nat.zero_le _
    simpa [c, h0] using ChainToRoot_zero hp
  have hcend : c (chainLength hp + 1) = q := by
    have hnot : ¬ chainLength hp + 1 ≤ chainLength hp := Nat.not_succ_le_self _
    simp [c, hnot]
  have hcmem : ∀ k ≤ chainLength hp + 1, c k ∈ T.Branches := by
    intro k hk
    by_cases hk_le : k ≤ chainLength hp
    · simpa [c, hk_le] using ChainToRoot_mem hp hk_le
    · have hk_last : k = chainLength hp + 1 := by omega
      simpa [c, hk_last, Nat.not_succ_le_self] using hq
  have hcstep :
      ∀ k < chainLength hp + 1,
        Combinatorial_Support (c (k + 1)) = (c k).1 ∨
        Combinatorial_Support (c (k + 1)) = (c k).2 := by
    intro k hk
    by_cases hk_lt : k < chainLength hp
    · have hk_le : k ≤ chainLength hp := Nat.le_of_lt hk_lt
      have hks_le : k + 1 ≤ chainLength hp := Nat.succ_le_of_lt hk_lt
      simpa [c, hk_le, hks_le] using ChainToRoot_step hp hk_lt
    · have hk_eq : k = chainLength hp := by omega
      have hk_le : k ≤ chainLength hp := by omega
      have hks_not : ¬ k + 1 ≤ chainLength hp := by omega
      have hc_k : c k = p := by
        simpa [c, hk_eq, hk_le] using ChainToRoot_end hp
      have hc_ks : c (k + 1) = q := by
        simpa [c, hks_not]
      rw [hc_k, hc_ks]
      exact Or.inl hqp
  have huniq := ChainToRoot_unique hq hc0 hcend hcmem hcstep
  omega

omit [MeasurableSpace α] in
lemma chainLength_eq_succ_of_support_eq_right
    [DecidableEq (Set α)]
    {T : BinaryTreeWithRootandTops (Set α)}
    {p q : Finset (Set α) × Finset (Set α)}
    (hp : p ∈ T.Branches) (hq : q ∈ T.Branches)
    (hqp : Combinatorial_Support q = p.2) :
    chainLength hq = chainLength hp + 1 := by
  let c : ℕ → Finset (Set α) × Finset (Set α) :=
    fun k => if h : k ≤ chainLength hp then ChainToRoot hp k else q
  have hc0 : c 0 = T.Root := by
    have h0 : 0 ≤ chainLength hp := Nat.zero_le _
    simpa [c, h0] using ChainToRoot_zero hp
  have hcend : c (chainLength hp + 1) = q := by
    have hnot : ¬ chainLength hp + 1 ≤ chainLength hp := Nat.not_succ_le_self _
    simp [c, hnot]
  have hcmem : ∀ k ≤ chainLength hp + 1, c k ∈ T.Branches := by
    intro k hk
    by_cases hk_le : k ≤ chainLength hp
    · simpa [c, hk_le] using ChainToRoot_mem hp hk_le
    · have hk_last : k = chainLength hp + 1 := by omega
      simpa [c, hk_last, Nat.not_succ_le_self] using hq
  have hcstep :
      ∀ k < chainLength hp + 1,
        Combinatorial_Support (c (k + 1)) = (c k).1 ∨
        Combinatorial_Support (c (k + 1)) = (c k).2 := by
    intro k hk
    by_cases hk_lt : k < chainLength hp
    · have hk_le : k ≤ chainLength hp := Nat.le_of_lt hk_lt
      have hks_le : k + 1 ≤ chainLength hp := Nat.succ_le_of_lt hk_lt
      simpa [c, hk_le, hks_le] using ChainToRoot_step hp hk_lt
    · have hk_eq : k = chainLength hp := by omega
      have hk_le : k ≤ chainLength hp := by omega
      have hks_not : ¬ k + 1 ≤ chainLength hp := by omega
      have hc_k : c k = p := by
        simpa [c, hk_eq, hk_le] using ChainToRoot_end hp
      have hc_ks : c (k + 1) = q := by
        simpa [c, hks_not]
      rw [hc_k, hc_ks]
      exact Or.inr hqp
  have huniq := ChainToRoot_unique hq hc0 hcend hcmem hcstep
  omega

/-- Local copy of the combinatorial existence lemma, using the ambient `DecidableEq`
instance for `Set α`. -/
lemma exists_branch_support_eq_left_of_two_le_card_local
    [DecidableEq (Set α)]
    {T : BinaryTreeWithRootandTops (Set α)}
    {p : Finset (Set α) × Finset (Set α)}
    (hp : p ∈ T.Branches)
    (hcard : 2 ≤ p.1.card)
    (childs_eq_tops : T.Childs = T.Tops) :
    ∃ q ∈ T.Branches, Combinatorial_Support q = p.1 := by
  have hp1_pos : 0 < p.1.card := lt_of_lt_of_le (by decide : 0 < 2) hcard
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hp1_pos
  have hx_childs : x ∈ T.Childs := (T.TreeStructureChilds p hp).1 hx
  have hx_tops : x ∈ T.Tops := by simpa [childs_eq_tops] using hx_childs
  obtain ⟨q, hq, hx_singleton⟩ := T.TopsareTops x hx_tops
  have hx_in_qsupport : x ∈ Combinatorial_Support q := singleton_in_support q hx_singleton
  have hq_ne_p : q ≠ p := by
    intro hqp
    subst hqp
    have hx_cases : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 := by
      dsimp [pairToFinset] at hx_singleton
      simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
    rcases hx_cases with hleft | hright
    · have hq1_card_one : q.1.card = 1 := by rw [← hleft]; simp
      omega
    · have hx_in_q2 : x ∈ q.2 := by
        rw [← hright]
        exact Finset.mem_singleton_self x
      exact (Finset.disjoint_left.mp (T.DisjointComponents q hq) hx hx_in_q2).elim
  have hq_sub_p1 : Combinatorial_Support q ⊆ p.1 := by
    rcases T.SupportProperty q hq p hp hq_ne_p with hdisj | hrest
    · exfalso
      have hx_in_psupport : x ∈ Combinatorial_Support p := Finset.mem_union_left p.2 hx
      exact Finset.disjoint_left.mp hdisj hx_in_qsupport hx_in_psupport
    rcases hrest with hq_sub_p1 | hrest
    · exact hq_sub_p1
    rcases hrest with hq_sub_p2 | hrest
    · exfalso
      have hx_in_p2 : x ∈ p.2 := hq_sub_p2 hx_in_qsupport
      exact Finset.disjoint_left.mp (T.DisjointComponents p hp) hx hx_in_p2
    rcases hrest with hp_sub_q1 | hp_sub_q2
    · exfalso
      have hx_in_psup : x ∈ Combinatorial_Support p := Finset.mem_union_left p.2 hx
      have hx_in_q1 : x ∈ q.1 := hp_sub_q1 hx_in_psup
      have hx_cases2 : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 := by
        dsimp [pairToFinset] at hx_singleton
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
      rcases hx_cases2 with hxeqq1 | hxeqq2
      · have hcard_q1 : q.1.card = 1 := by rw [← hxeqq1]; simp
        have : p.1.card ≤ q.1.card :=
          Finset.card_le_card (Finset.subset_union_left.trans hp_sub_q1)
        omega
      · have hx_in_q2 : x ∈ q.2 := hxeqq2 ▸ Finset.mem_singleton_self x
        exact absurd hx_in_q2 (Finset.disjoint_left.mp (T.DisjointComponents q hq) hx_in_q1)
    · exfalso
      have hx_in_psup : x ∈ Combinatorial_Support p := Finset.mem_union_left p.2 hx
      have hx_in_q2 : x ∈ q.2 := hp_sub_q2 hx_in_psup
      have hx_cases2 : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 := by
        dsimp [pairToFinset] at hx_singleton
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
      rcases hx_cases2 with hxeqq1 | hxeqq2
      · have hx_in_q1 : x ∈ q.1 := hxeqq1 ▸ Finset.mem_singleton_self x
        exact absurd hx_in_q2 (Finset.disjoint_left.mp (T.DisjointComponents q hq) hx_in_q1)
      · have hcard_q2 : q.2.card = 1 := by rw [← hxeqq2]; simp
        have : p.1.card ≤ q.2.card :=
          Finset.card_le_card (Finset.subset_union_left.trans hp_sub_q2)
        omega
  exact maximal_compact_inside_p1 hp ⟨q, hq, hq_sub_p1⟩

/-- Local copy of the right-side combinatorial existence lemma, using the ambient
`DecidableEq` instance for `Set α`. -/
lemma exists_branch_support_eq_right_of_two_le_card_local
    [DecidableEq (Set α)]
    {T : BinaryTreeWithRootandTops (Set α)}
    {p : Finset (Set α) × Finset (Set α)}
    (hp : p ∈ T.Branches)
    (hcard : 2 ≤ p.2.card)
    (childs_eq_tops : T.Childs = T.Tops) :
    ∃ q ∈ T.Branches, Combinatorial_Support q = p.2 := by
  have hp2_pos : 0 < p.2.card := lt_of_lt_of_le (by decide : 0 < 2) hcard
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hp2_pos
  have hx_childs : x ∈ T.Childs := (T.TreeStructureChilds p hp).2 hx
  have hx_tops : x ∈ T.Tops := by simpa [childs_eq_tops] using hx_childs
  obtain ⟨q, hq, hx_singleton⟩ := T.TopsareTops x hx_tops
  have hx_in_qsupport : x ∈ Combinatorial_Support q := singleton_in_support q hx_singleton
  have hq_ne_p : q ≠ p := by
    intro hqp
    subst hqp
    have hx_cases : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 := by
      dsimp [pairToFinset] at hx_singleton
      simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
    rcases hx_cases with hleft | hright
    · have hx_in_q1 : x ∈ q.1 := hleft ▸ Finset.mem_singleton_self x
      exact absurd hx (Finset.disjoint_left.mp (T.DisjointComponents q hq) hx_in_q1)
    · have hq2_card_one : q.2.card = 1 := by rw [← hright]; simp
      omega
  have hq_sub_p2 : Combinatorial_Support q ⊆ p.2 := by
    rcases T.SupportProperty q hq p hp hq_ne_p with hdisj | hrest
    · exfalso
      have hx_in_psupport : x ∈ Combinatorial_Support p := Finset.mem_union_right p.1 hx
      exact Finset.disjoint_left.mp hdisj hx_in_qsupport hx_in_psupport
    rcases hrest with hq_sub_p1 | hrest
    · exfalso
      have hx_in_p1 : x ∈ p.1 := hq_sub_p1 hx_in_qsupport
      exact absurd hx (Finset.disjoint_left.mp (T.DisjointComponents p hp) hx_in_p1)
    rcases hrest with hq_sub_p2 | hrest
    · exact hq_sub_p2
    rcases hrest with hp_sub_q1 | hp_sub_q2
    · exfalso
      have hx_in_psup : x ∈ Combinatorial_Support p := Finset.mem_union_right p.1 hx
      have hx_in_q1 : x ∈ q.1 := hp_sub_q1 hx_in_psup
      have hx_cases2 : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 := by
        dsimp [pairToFinset] at hx_singleton
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
      rcases hx_cases2 with hxeqq1 | hxeqq2
      · have hcard_q1 : q.1.card = 1 := by rw [← hxeqq1]; simp
        have : p.2.card ≤ q.1.card :=
          Finset.card_le_card (Finset.subset_union_right.trans hp_sub_q1)
        omega
      · have hx_in_q2 : x ∈ q.2 := hxeqq2 ▸ Finset.mem_singleton_self x
        exact absurd hx_in_q2 (Finset.disjoint_left.mp (T.DisjointComponents q hq) hx_in_q1)
    · exfalso
      have hx_in_psup : x ∈ Combinatorial_Support p := Finset.mem_union_right p.1 hx
      have hx_in_q2 : x ∈ q.2 := hp_sub_q2 hx_in_psup
      have hx_cases2 : ({x} : Finset (Set α)) = q.1 ∨ ({x} : Finset (Set α)) = q.2 := by
        dsimp [pairToFinset] at hx_singleton
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx_singleton
      rcases hx_cases2 with hxeqq1 | hxeqq2
      · have hx_in_q1 : x ∈ q.1 := hxeqq1 ▸ Finset.mem_singleton_self x
        exact absurd hx_in_q2 (Finset.disjoint_left.mp (T.DisjointComponents q hq) hx_in_q1)
      · have hcard_q2 : q.2.card = 1 := by rw [← hxeqq2]; simp
        have : p.2.card ≤ q.2.card :=
          Finset.card_le_card (Finset.subset_union_right.trans hp_sub_q2)
        omega
  exact maximal_compact_inside_p2 hp ⟨q, hq, hq_sub_p2⟩

lemma HaarSystem.Index.left_branchSupport_mem_nodesAtDeepness_succ
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    UnbalancedHaarWavelet.branchSupport i.branch.1.1 ∈
      H.nodesAtDeepness G (i.deepness G H + 1) := by
  classical
  rcases i with ⟨level, cell, hcell, branch⟩
  let T := H.binaryRefinement.tree level cell hcell
  let parentIndex : H.Index :=
    { level := level
      cell := cell
      hcell := hcell
      branch := branch }
  have hchilds_eq_tops : T.Childs = T.Tops := by
    ext s
    constructor
    · intro hs
      exact (H.binaryRefinement.tops_are_children level cell hcell s).2
        ((H.binaryRefinement.childs_are_children level cell hcell s).1 hs)
    · intro hs
      exact (H.binaryRefinement.childs_are_children level cell hcell s).2
        ((H.binaryRefinement.tops_are_children level cell hcell s).1 hs)
  by_cases hcard : 2 ≤ branch.1.1.card
  · have hbranch_mem : branch.1 ∈ T.Branches := by
      simpa [T] using branch.2
    rcases exists_branch_support_eq_left_of_two_le_card_local
      (T := T) (p := branch.1) hbranch_mem hcard hchilds_eq_tops with
        ⟨q, hq, hq_support⟩
    let j : H.Index :=
      { level := level
        cell := cell
        hcell := hcell
        branch := ⟨q, hq⟩ }
    refine ⟨j, ?_, ?_⟩
    · dsimp [j, HaarSystem.Index.branchSupport]
      simpa [haarBranchSupport, hq_support]
    · have hstep :
          haarBranchSupport j.branch.1 =
            UnbalancedHaarWavelet.branchSupport parentIndex.branch.1.1 ∨
          haarBranchSupport j.branch.1 =
            UnbalancedHaarWavelet.branchSupport parentIndex.branch.1.2 := by
        left
        dsimp [j, parentIndex]
        simpa [haarBranchSupport, hq_support]
      have hdeep :=
        HaarSystem.Index.deepness_eq_succ_of_haarBranchSupport_eq_side
          G H parentIndex j hstep
      simpa [j, parentIndex] using hdeep
  · have hsingleton : ∃ s : Set α, branch.1.1 = {s} := by
      have hne : branch.1.1.Nonempty :=
        (T.NonemptyPairs branch.1 branch.2).1
      have hpos : 0 < branch.1.1.card := Finset.card_pos.mpr hne
      have hle : branch.1.1.card ≤ 1 := by omega
      exact Finset.card_eq_one.mp (Nat.le_antisymm hle hpos)
    rcases hsingleton with ⟨s, hs⟩
    have hp_childs : branch.1.1 ⊆ T.Childs ∧ branch.1.2 ⊆ T.Childs :=
      T.TreeStructureChilds branch.1 branch.2
    have hs_left : s ∈ branch.1.1 := by
      simpa [hs]
    have hs_child : s ∈ G.children level cell :=
      (H.binaryRefinement.childs_are_children level cell hcell s).1
        (hp_childs.1 hs_left)
    have hs_part : s ∈ G.grid.partitions (level + 1) := hs_child.1
    have hs_support :
        UnbalancedHaarWavelet.branchSupport branch.1.1 = s := by
      simpa [hs] using (branchSupport_singleton (α := α) s)
    let Tchild := H.binaryRefinement.tree (level + 1) s hs_part
    let j : H.Index :=
      { level := level + 1
        cell := s
        hcell := hs_part
        branch := ⟨Tchild.Root, Tchild.RootinBranches⟩ }
    refine ⟨j, ?_, ?_⟩
    · dsimp [j, HaarSystem.Index.branchSupport, Tchild]
      exact (H.haarBranchSupport_root_eq_cell G
        (level := level + 1) (cell := s) (hcell := hs_part)).trans hs_support.symm
    · have hstep :
          haarBranchSupport j.branch.1 =
            UnbalancedHaarWavelet.branchSupport parentIndex.branch.1.1 ∨
          haarBranchSupport j.branch.1 =
            UnbalancedHaarWavelet.branchSupport parentIndex.branch.1.2 := by
        left
        dsimp [j, parentIndex, Tchild]
        exact (H.haarBranchSupport_root_eq_cell G
          (level := level + 1) (cell := s) (hcell := hs_part)).trans hs_support.symm
      have hdeep :=
        HaarSystem.Index.deepness_eq_succ_of_haarBranchSupport_eq_side
          G H parentIndex j hstep
      simpa [j, parentIndex] using hdeep

lemma HaarSystem.Index.right_branchSupport_mem_nodesAtDeepness_succ
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    UnbalancedHaarWavelet.branchSupport i.branch.1.2 ∈
      H.nodesAtDeepness G (i.deepness G H + 1) := by
  classical
  rcases i with ⟨level, cell, hcell, branch⟩
  let T := H.binaryRefinement.tree level cell hcell
  let parentIndex : H.Index :=
    { level := level
      cell := cell
      hcell := hcell
      branch := branch }
  have hchilds_eq_tops : T.Childs = T.Tops := by
    ext s
    constructor
    · intro hs
      exact (H.binaryRefinement.tops_are_children level cell hcell s).2
        ((H.binaryRefinement.childs_are_children level cell hcell s).1 hs)
    · intro hs
      exact (H.binaryRefinement.childs_are_children level cell hcell s).2
        ((H.binaryRefinement.tops_are_children level cell hcell s).1 hs)
  by_cases hcard : 2 ≤ branch.1.2.card
  · have hbranch_mem : branch.1 ∈ T.Branches := by
      simpa [T] using branch.2
    rcases exists_branch_support_eq_right_of_two_le_card_local
      (T := T) (p := branch.1) hbranch_mem hcard hchilds_eq_tops with
        ⟨q, hq, hq_support⟩
    let j : H.Index :=
      { level := level
        cell := cell
        hcell := hcell
        branch := ⟨q, hq⟩ }
    refine ⟨j, ?_, ?_⟩
    · dsimp [j, HaarSystem.Index.branchSupport]
      simpa [haarBranchSupport, hq_support]
    · have hstep :
          haarBranchSupport j.branch.1 =
            UnbalancedHaarWavelet.branchSupport parentIndex.branch.1.1 ∨
          haarBranchSupport j.branch.1 =
            UnbalancedHaarWavelet.branchSupport parentIndex.branch.1.2 := by
        right
        dsimp [j, parentIndex]
        simpa [haarBranchSupport, hq_support]
      have hdeep :=
        HaarSystem.Index.deepness_eq_succ_of_haarBranchSupport_eq_side
          G H parentIndex j hstep
      simpa [j, parentIndex] using hdeep
  · have hsingleton : ∃ s : Set α, branch.1.2 = {s} := by
      have hne : branch.1.2.Nonempty :=
        (T.NonemptyPairs branch.1 branch.2).2
      have hpos : 0 < branch.1.2.card := Finset.card_pos.mpr hne
      have hle : branch.1.2.card ≤ 1 := by omega
      exact Finset.card_eq_one.mp (Nat.le_antisymm hle hpos)
    rcases hsingleton with ⟨s, hs⟩
    have hp_childs : branch.1.1 ⊆ T.Childs ∧ branch.1.2 ⊆ T.Childs :=
      T.TreeStructureChilds branch.1 branch.2
    have hs_right : s ∈ branch.1.2 := by
      simpa [hs]
    have hs_child : s ∈ G.children level cell :=
      (H.binaryRefinement.childs_are_children level cell hcell s).1
        (hp_childs.2 hs_right)
    have hs_part : s ∈ G.grid.partitions (level + 1) := hs_child.1
    have hs_support :
        UnbalancedHaarWavelet.branchSupport branch.1.2 = s := by
      simpa [hs] using (branchSupport_singleton (α := α) s)
    let Tchild := H.binaryRefinement.tree (level + 1) s hs_part
    let j : H.Index :=
      { level := level + 1
        cell := s
        hcell := hs_part
        branch := ⟨Tchild.Root, Tchild.RootinBranches⟩ }
    refine ⟨j, ?_, ?_⟩
    · dsimp [j, HaarSystem.Index.branchSupport, Tchild]
      exact (H.haarBranchSupport_root_eq_cell G
        (level := level + 1) (cell := s) (hcell := hs_part)).trans hs_support.symm
    · have hstep :
          haarBranchSupport j.branch.1 =
            UnbalancedHaarWavelet.branchSupport parentIndex.branch.1.1 ∨
          haarBranchSupport j.branch.1 =
            UnbalancedHaarWavelet.branchSupport parentIndex.branch.1.2 := by
        right
        dsimp [j, parentIndex, Tchild]
        exact (H.haarBranchSupport_root_eq_cell G
          (level := level + 1) (cell := s) (hcell := hs_part)).trans hs_support.symm
      have hdeep :=
        HaarSystem.Index.deepness_eq_succ_of_haarBranchSupport_eq_side
          G H parentIndex j hstep
      simpa [j, parentIndex] using hdeep

lemma HaarSystem.nodesAtDeepness_zero_eq_singleton
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    H.nodesAtDeepness G 0 = {Set.univ} := by
  classical
  ext S
  constructor
  · intro hS
    rcases hS with ⟨i, hiS, hideep⟩
    let h_exists := H.exists_LongChain_to_Root_finish_branch G i.hcell i.branch.2
    let chain := Classical.choose (Classical.choose_spec h_exists)
    have hchosen :
        LongChain_to_Root G H (i.deepness G H) chain ∧
          chain (i.deepness G H) = i.branch.1 := by
      simpa [HaarSystem.Index.deepness, h_exists, chain] using
        (Classical.choose_spec (Classical.choose_spec h_exists))
    have hbranch_root :
        i.branch.1 =
          (H.binaryRefinement.tree 0 (Set.univ : Set α)
            (by simp [G.grid.first_partition_eq_univ])).Root := by
      have hend0 : chain 0 = i.branch.1 := by simpa [hideep] using hchosen.2
      exact hend0.symm.trans hchosen.1.1
    have hi_univ : i.branchSupport G H = Set.univ := by
      dsimp [HaarSystem.Index.branchSupport]
      rw [hbranch_root]
      exact H.haarBranchSupport_root_eq_cell G
        (level := 0) (cell := (Set.univ : Set α))
        (hcell := by simp [G.grid.first_partition_eq_univ])
    simp [← hiS, hi_univ]
  · intro hS
    simp at hS
    subst S
    simpa using H.branchSupport_mem_nodesAtDeepness G (H.rootIndex G)

lemma HaarSystem.nodesAtDeepness_eq_or_disjoint
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (n : ℕ) (S₁ S₂ : Set α)
    (hS₁ : S₁ ∈ H.nodesAtDeepness G n)
    (hS₂ : S₂ ∈ H.nodesAtDeepness G n) :
    S₁ = S₂ ∨ Disjoint S₁ S₂ := by
  classical
  rcases hS₁ with ⟨i, hiS, hideep_i⟩
  rcases hS₂ with ⟨j, hjS, hideep_j⟩
  let h_exists_i := H.exists_LongChain_to_Root_finish_branch G i.hcell i.branch.2
  let chain_i := Classical.choose (Classical.choose_spec h_exists_i)
  have hchosen_i :
      LongChain_to_Root G H n chain_i ∧ chain_i n = i.branch.1 := by
    have hchosen :
        LongChain_to_Root G H (i.deepness G H) chain_i ∧
          chain_i (i.deepness G H) = i.branch.1 := by
      simpa [HaarSystem.Index.deepness, h_exists_i, chain_i] using
        (Classical.choose_spec (Classical.choose_spec h_exists_i))
    simpa [hideep_i] using hchosen
  let h_exists_j := H.exists_LongChain_to_Root_finish_branch G j.hcell j.branch.2
  let chain_j := Classical.choose (Classical.choose_spec h_exists_j)
  have hchosen_j :
      LongChain_to_Root G H n chain_j ∧ chain_j n = j.branch.1 := by
    have hchosen :
        LongChain_to_Root G H (j.deepness G H) chain_j ∧
          chain_j (j.deepness G H) = j.branch.1 := by
      simpa [HaarSystem.Index.deepness, h_exists_j, chain_j] using
        (Classical.choose_spec (Classical.choose_spec h_exists_j))
    simpa [hideep_j] using hchosen
  rcases LongChain_to_Root.eq_or_disjoint_final_of_same_length
      G H hchosen_i.1 hchosen_j.1 with heq | hdisj
  · left
    rw [← hiS, ← hjS]
    dsimp [HaarSystem.Index.branchSupport]
    simpa [hchosen_i.2, hchosen_j.2] using heq
  · right
    rw [← hiS, ← hjS]
    dsimp [HaarSystem.Index.branchSupport]
    simpa [hchosen_i.2, hchosen_j.2] using hdisj

lemma HaarSystem.binaryChildren_unique_up_to_swap
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {n : ℕ} {S : Set α} {AB CD : Set α × Set α}
    (hAB_ne : AB.1 ≠ AB.2)
    (hAB1 : AB.1 ∈ H.nodesAtDeepness G (n + 1))
    (hAB2 : AB.2 ∈ H.nodesAtDeepness G (n + 1))
    (hAB1_sub : AB.1 ⊆ S) (hAB2_sub : AB.2 ⊆ S)
    (hAB_union : S = AB.1 ∪ AB.2)
    (hAB_disj : Disjoint AB.1 AB.2)
    (hCD_ne : CD.1 ≠ CD.2)
    (hCD1 : CD.1 ∈ H.nodesAtDeepness G (n + 1))
    (hCD2 : CD.2 ∈ H.nodesAtDeepness G (n + 1))
    (hCD1_sub : CD.1 ⊆ S) (hCD2_sub : CD.2 ⊆ S)
    (hCD_union : S = CD.1 ∪ CD.2)
    (hCD_disj : Disjoint CD.1 CD.2) :
    CD = AB ∨ CD = (AB.2, AB.1) := by
  classical
  have hCD1_nonempty : CD.1.Nonempty := by
    by_contra h_empty
    have h_eq_empty : CD.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp h_empty
    have hμ_zero : G.μ CD.1 = 0 := by simp [h_eq_empty]
    have hμ_pos : 0 < G.μ CD.1 :=
      H.measure_pos_of_mem_nodesAtDeepness G hCD1
    rw [hμ_zero] at hμ_pos
    exact (lt_irrefl 0 hμ_pos).elim
  have hCD1_eq_left_or_right : CD.1 = AB.1 ∨ CD.1 = AB.2 := by
    have hleft := H.nodesAtDeepness_eq_or_disjoint G (n + 1) CD.1 AB.1 hCD1 hAB1
    have hright := H.nodesAtDeepness_eq_or_disjoint G (n + 1) CD.1 AB.2 hCD1 hAB2
    rcases hleft with hleft_eq | hleft_disj
    · exact Or.inl hleft_eq
    rcases hright with hright_eq | hright_disj
    · exact Or.inr hright_eq
    exfalso
    rcases hCD1_nonempty with ⟨x, hx⟩
    have hxS : x ∈ S := hCD1_sub hx
    have hxAB : x ∈ AB.1 ∪ AB.2 := by simpa [hAB_union] using hxS
    rcases hxAB with hxAB1 | hxAB2
    · exact (Set.disjoint_left.mp hleft_disj hx hxAB1).elim
    · exact (Set.disjoint_left.mp hright_disj hx hxAB2).elim
  rcases hCD1_eq_left_or_right with hCD1_left | hCD1_right
  · left
    have hCD2_right : CD.2 = AB.2 := by
      ext x
      constructor
      · intro hx
        have hxS : x ∈ S := hCD2_sub hx
        have hxAB : x ∈ AB.1 ∪ AB.2 := by simpa [hAB_union] using hxS
        rcases hxAB with hxAB1 | hxAB2
        · have hxCD1 : x ∈ CD.1 := by simpa [hCD1_left] using hxAB1
          exact (Set.disjoint_left.mp hCD_disj hxCD1 hx).elim
        · exact hxAB2
      · intro hx
        have hxS : x ∈ S := by
          rw [hAB_union]
          exact Or.inr hx
        have hxCD : x ∈ CD.1 ∪ CD.2 := by simpa [hCD_union] using hxS
        rcases hxCD with hxCD1 | hxCD2
        · have hxAB1 : x ∈ AB.1 := by simpa [hCD1_left] using hxCD1
          exact (Set.disjoint_left.mp hAB_disj hxAB1 hx).elim
        · exact hxCD2
    ext <;> simp [hCD1_left, hCD2_right]
  · right
    have hCD2_left : CD.2 = AB.1 := by
      ext x
      constructor
      · intro hx
        have hxS : x ∈ S := hCD2_sub hx
        have hxAB : x ∈ AB.1 ∪ AB.2 := by simpa [hAB_union] using hxS
        rcases hxAB with hxAB1 | hxAB2
        · exact hxAB1
        · have hxCD1 : x ∈ CD.1 := by simpa [hCD1_right] using hxAB2
          exact (Set.disjoint_left.mp hCD_disj hxCD1 hx).elim
      · intro hx
        have hxS : x ∈ S := by
          rw [hAB_union]
          exact Or.inl hx
        have hxCD : x ∈ CD.1 ∪ CD.2 := by simpa [hCD_union] using hxS
        rcases hxCD with hxCD1 | hxCD2
        · have hxAB2 : x ∈ AB.2 := by simpa [hCD1_right] using hxCD1
          exact (Set.disjoint_left.mp hAB_disj hx hxAB2).elim
        · exact hxCD2
    ext <;> simp [hCD1_right, hCD2_left]








/-- Estrutura da sequência de partições induzidas pelos suportes dos ramos do sistema de Haar.
    - A partição de nível zero é {univ}.
    - Nós de mesma profundidade são iguais ou disjuntos.
    - Cada suporte S de profundidade n é suporte de algum branch p,
      e seus dois lados A e B aparecem na profundidade n+1.
    - Se S = supp(p), então S = A ∪ B com A e B disjuntos.
    - Novo: se (a,b) é branch de alguma subtree, então haarBranchSupport (a,b)
      pertence a alguma partição (nodesAtDeepness). -/
theorem HaarSystem.binaryGrid_structure
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
  H.nodesAtDeepness G 0 = {Set.univ} ∧
  (∀ n S₁ S₂,
    S₁ ∈ H.nodesAtDeepness G n → S₂ ∈ H.nodesAtDeepness G n →
    S₁ = S₂ ∨ Disjoint S₁ S₂) ∧
  (∀ n S, S ∈ H.nodesAtDeepness G n →
    (∃ AB : Set α × Set α,
      AB.1 ≠ AB.2 ∧
      AB.1 ∈ H.nodesAtDeepness G (n + 1) ∧
      AB.2 ∈ H.nodesAtDeepness G (n + 1) ∧
      AB.1 ⊆ S ∧ AB.2 ⊆ S ∧
      S = AB.1 ∪ AB.2 ∧ Disjoint AB.1 AB.2 ∧
      ∀ CD : Set α × Set α,
        CD.1 ≠ CD.2 →
        CD.1 ∈ H.nodesAtDeepness G (n + 1) →
        CD.2 ∈ H.nodesAtDeepness G (n + 1) →
        CD.1 ⊆ S → CD.2 ⊆ S →
        S = CD.1 ∪ CD.2 → Disjoint CD.1 CD.2 →
        CD = AB ∨ CD = (AB.2, AB.1))) ∧
  (∀ n S,
    S ∈ H.nodesAtDeepness G n →
    ∃ (i : H.Index) (p : Finset (Set α) × Finset (Set α)),
        i.branchSupport G H = S ∧
        p ∈ (H.binaryRefinement.tree i.level i.cell i.hcell).Branches ∧
        S = haarBranchSupport p ∧
        let A := UnbalancedHaarWavelet.branchSupport p.1
        let B := UnbalancedHaarWavelet.branchSupport p.2
        A ∈ H.nodesAtDeepness G (n + 1) ∧ B ∈ H.nodesAtDeepness G (n + 1) ∧
        A ⊆ S ∧ B ⊆ S ∧
        S = A ∪ B ∧ Disjoint A B) ∧
  (∀ level cell (hcell : cell ∈ G.grid.partitions level)
      (p : Finset (Set α) × Finset (Set α)),
      p ∈ (H.binaryRefinement.tree level cell hcell).Branches →
      ∃ n, haarBranchSupport p ∈ H.nodesAtDeepness G n) := by
  classical
  have hnode_split :
      ∀ n S,
        S ∈ H.nodesAtDeepness G n →
        ∃ (i : H.Index) (p : Finset (Set α) × Finset (Set α)),
            i.branchSupport G H = S ∧
            p ∈ (H.binaryRefinement.tree i.level i.cell i.hcell).Branches ∧
            S = haarBranchSupport p ∧
            let A := UnbalancedHaarWavelet.branchSupport p.1
            let B := UnbalancedHaarWavelet.branchSupport p.2
            A ∈ H.nodesAtDeepness G (n + 1) ∧ B ∈ H.nodesAtDeepness G (n + 1) ∧
            A ⊆ S ∧ B ⊆ S ∧
            S = A ∪ B ∧ Disjoint A B := by
    intro n S hS
    rcases hS with ⟨i, hiS, hideep⟩
    refine ⟨i, i.branch.1, hiS, i.branch.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [HaarSystem.Index.branchSupport] using hiS.symm
    · simpa [hideep] using i.left_branchSupport_mem_nodesAtDeepness_succ G H
    · simpa [hideep] using i.right_branchSupport_mem_nodesAtDeepness_succ G H
    · rw [← hiS]
      exact branchSupport_left_subset_haarBranchSupport i.branch.1
    · rw [← hiS]
      exact branchSupport_right_subset_haarBranchSupport i.branch.1
    · rw [← hiS]
      exact haarBranchSupport_eq_union_branchSupport i.branch.1
    · simpa using H.branchSupport_components_disjoint G i.branch
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact H.nodesAtDeepness_zero_eq_singleton G
  · intro n S₁ S₂ hS₁ hS₂
    exact H.nodesAtDeepness_eq_or_disjoint G n S₁ S₂ hS₁ hS₂
  · intro n S hS
    rcases hnode_split n S hS with
      ⟨i, p, hiS, hp, hS_eq, hA_mem, hB_mem, hA_sub, hB_sub, hunion, hdisj⟩
    have hAB_ne :
        UnbalancedHaarWavelet.branchSupport p.1 ≠
          UnbalancedHaarWavelet.branchSupport p.2 := by
      intro h_eq
      let T := H.binaryRefinement.tree i.level i.cell i.hcell
      have hp_childs : p.1 ⊆ T.Childs ∧ p.2 ⊆ T.Childs :=
        T.TreeStructureChilds p hp
      have hp1_part :
          ∀ s, s ∈ p.1 → s ∈ G.grid.partitions (i.level + 1) := by
        intro s hs
        exact (H.binaryRefinement.childs_are_children i.level i.cell i.hcell s).1
          (hp_childs.1 hs) |>.1
      have hpos_left : 0 < G.μ (UnbalancedHaarWavelet.branchSupport p.1) := by
        exact measure_branchSupport_pos_of_nonempty G p.1
          (by
            intro s hs
            exact G.positive_measure (i.level + 1) s (hp1_part s hs))
          (T.NonemptyPairs p hp).1
      have hdisj_self :
          Disjoint (UnbalancedHaarWavelet.branchSupport p.1)
            (UnbalancedHaarWavelet.branchSupport p.1) := by
        simpa [h_eq] using hdisj
      have hleft_empty : UnbalancedHaarWavelet.branchSupport p.1 = ∅ := by
        simpa [disjoint_self] using hdisj_self
      have hmeasure_zero : G.μ (UnbalancedHaarWavelet.branchSupport p.1) = 0 := by
        simp [hleft_empty]
      rw [hmeasure_zero] at hpos_left
      exact (lt_irrefl 0 hpos_left).elim
    refine ⟨
      (UnbalancedHaarWavelet.branchSupport p.1,
        UnbalancedHaarWavelet.branchSupport p.2),
      hAB_ne, hA_mem, hB_mem, hA_sub, hB_sub, hunion, hdisj, ?_⟩
    intro CD hCD_ne hCD1 hCD2 hCD1_sub hCD2_sub hCD_union hCD_disj
    exact H.binaryChildren_unique_up_to_swap G
      (AB := (UnbalancedHaarWavelet.branchSupport p.1,
        UnbalancedHaarWavelet.branchSupport p.2))
      (CD := CD) (n := n) (S := S)
      hAB_ne hA_mem hB_mem hA_sub hB_sub hunion hdisj
      hCD_ne hCD1 hCD2 hCD1_sub hCD2_sub hCD_union hCD_disj
  · intro n S hS
    exact hnode_split n S hS
  · intro level cell hcell p hp
    let i : H.Index :=
      { level := level
        cell := cell
        hcell := hcell
        branch := ⟨p, hp⟩ }
    refine ⟨i.deepness G H, ?_⟩
    simpa [i, HaarSystem.Index.branchSupport] using
      H.branchSupport_mem_nodesAtDeepness G i





end UnbalancedHaarWavelet
