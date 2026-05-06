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

open scoped Classical

/-- The set-theoretic support associated with a branch, i.e. the union of all grid cells
appearing in its two sides. -/
noncomputable def haarBranchSupport [DecidableEq (Set α)]
    (p : Finset (Set α) × Finset (Set α)) : Set α :=
  branchSupport (Combinatorial_Support p)

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
    (hA_sub : A ⊆ branchSupport q.1.1) :
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
  let B₁ := branchSupport q.1.1
  let B₂ := branchSupport q.1.2
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
    (hA_sub : A ⊆ branchSupport q.1.2) :
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
  let B₁ := branchSupport q.1.1
  let B₂ := branchSupport q.1.2
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
      let B₁ := branchSupport b.1
      let B₂ := branchSupport b.2
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
      let B₁ := branchSupport b.1
      let B₂ := branchSupport b.2
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
      have hsub_side : haarBranchSupport p.1 ⊆ branchSupport q.1.1 :=
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
        have hsub_side : haarBranchSupport p.1 ⊆ branchSupport q.1.2 :=
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
        have hc_q1_disj : Disjoint c (branchSupport q.1.1) := by
          refine Set.disjoint_left.2 ?_
          intro x hxc hxq
          rcases (by simpa [branchSupport] using hxq) with ⟨s, hs, hxs⟩
          have hs_ne : s ≠ c := by
            intro hsc
            exact hc_q1 (hsc ▸ hs)
          have hs_disj : Disjoint s c :=
            G.grid.disjoint (n + 1) s c (hq1_part s hs) hc_child.1 hs_ne
          exact (Set.disjoint_left.mp hs_disj hxs hxc).elim
        have hc_q2_disj : Disjoint c (branchSupport q.1.2) := by
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
        = branchSupport (Combinatorial_Support T.Root) := by rfl
    _ = branchSupport T.Childs := by rw [hroot_childs]
    _ = branchSupport (G.childrenFinset level cell) := by rw [hchilds_finset]
    _ = cell := HaarSystem.branchSupport_childrenFinset_eq G level cell hcell

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

/-- The deepness of a globally indexed Haar branch.

`cellDeepness G H n Q hQ` is the depth of the root support of the grid cell `Q` in the
binary grid induced by the Haar-system refinements. Passing from a parent cell to one of its
children adds the length of the chain in the parent's binary tree down to the branch whose side
is that child, plus one final edge from that branch to the side. -/
noncomputable def HaarSystem.cellDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    ∀ (level : ℕ) (cell : Set α), cell ∈ G.grid.partitions level → ℕ
  | 0, _cell, _hcell => 0
  | level + 1, cell, hcell =>
      let parent : Set α := Classical.choose (G.grid.nested level cell hcell)
      have hparent : parent ∈ G.grid.partitions level :=
        (Classical.choose_spec (G.grid.nested level cell hcell)).1
      have hcell_parent : cell ⊆ parent :=
        (Classical.choose_spec (G.grid.nested level cell hcell)).2
      let T := H.binaryRefinement.tree level parent hparent
      have hchild : cell ∈ G.children level parent := ⟨hcell, hcell_parent⟩
      have htop : cell ∈ T.Tops :=
        (H.binaryRefinement.tops_are_children level parent hparent cell).2 hchild
      let parentBranch : Finset (Set α) × Finset (Set α) :=
        Classical.choose (T.TopsareTops cell htop)
      have hparentBranch : parentBranch ∈ T.Branches :=
        (Classical.choose_spec (T.TopsareTops cell htop)).1
      H.cellDeepness G level parent hparent + chainLength hparentBranch + 1

lemma HaarSystem.cellDeepness_chosenParent_lt_child
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {child : Set α}
    (hchild : child ∈ G.grid.partitions (level + 1)) :
    let parent : Set α := Classical.choose (G.grid.nested level child hchild)
    let hparent : parent ∈ G.grid.partitions level :=
      (Classical.choose_spec (G.grid.nested level child hchild)).1
    H.cellDeepness G level parent hparent
      < H.cellDeepness G (level + 1) child hchild := by
  classical
  dsimp [HaarSystem.cellDeepness]
  omega

lemma HaarSystem.exists_parent_cellDeepness_lt
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {child : Set α}
    (hchild : child ∈ G.grid.partitions (level + 1)) :
    ∃ parent : Set α, ∃ hparent : parent ∈ G.grid.partitions level,
      child ⊆ parent ∧
      H.cellDeepness G level parent hparent
        < H.cellDeepness G (level + 1) child hchild := by
  classical
  let parent : Set α := Classical.choose (G.grid.nested level child hchild)
  have hparent : parent ∈ G.grid.partitions level :=
    (Classical.choose_spec (G.grid.nested level child hchild)).1
  have hchild_parent : child ⊆ parent :=
    (Classical.choose_spec (G.grid.nested level child hchild)).2
  refine ⟨parent, hparent, hchild_parent, ?_⟩
  exact H.cellDeepness_chosenParent_lt_child G hchild

lemma HaarSystem.cellDeepness_pos_of_positive_level
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α}
    (hcell : cell ∈ G.grid.partitions (level + 1)) :
    0 < H.cellDeepness G (level + 1) cell hcell := by
  rcases H.exists_parent_cellDeepness_lt G hcell with
    ⟨parent, hparent, hcell_parent, hlt⟩
  omega

/-- The deepness of a globally indexed Haar branch.

It is the induced-binary-grid depth of the ambient grid cell plus the length of the chain inside
that cell's binary refinement tree from its root branch to the chosen branch. -/
noncomputable def HaarSystem.Index.deepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) : ℕ :=
  H.cellDeepness G i.level i.cell i.hcell + chainLength i.branch.2

@[simp]
lemma HaarSystem.Index.deepness_mk
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (level : ℕ) (cell : Set α) (hcell : cell ∈ G.grid.partitions level)
    (branch : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree level cell hcell).Branches}) :
    (HaarSystem.Index.deepness G H
      ({ level := level, cell := cell, hcell := hcell, branch := branch } : H.Index))
      = H.cellDeepness G level cell hcell + chainLength branch.2 := by
  rfl

lemma HaarSystem.Index.cellDeepness_le_deepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    H.cellDeepness G i.level i.cell i.hcell ≤ i.deepness G H := by
  dsimp [HaarSystem.Index.deepness]
  omega

lemma HaarSystem.Index.branchSupport_subset_ambient_cell
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    i.branchSupport G H ⊆ i.cell := by
  rcases i with ⟨level, cell, hcell, branch⟩
  exact H.haarBranchSupport_subset_cell G branch

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
  · dsimp [parentIndex, HaarSystem.Index.deepness, parentBranch]
    have hparent_len : chainLength hparent_mem = chainLength branch.2 - 1 := by
      symm
      exact chainLength_eq_of_chainToRoot_eq branch.2 hparent_mem hparent_le rfl
    have hpred : chainLength branch.2 - 1 + 1 = chainLength branch.2 :=
      Nat.succ_pred_eq_of_pos hpos
    rw [hparent_len, Nat.add_assoc, hpred]
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
  dsimp [HaarSystem.rootIndex, HaarSystem.Index.deepness, HaarSystem.cellDeepness]
  simp [HaarSystem.chainLength_root]

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

This includes both internal Haar-branch supports and grid cells. The grid-cell nodes are needed
because a side of a local binary tree may already be a top/leaf, hence it is not itself the
support of another Haar branch. -/
noncomputable def HaarSystem.nodesAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n : ℕ) : Set (Set α) :=
  {S |
    (∃ i : H.Index, i.branchSupport G H = S ∧ i.deepness G H = n) ∨
    (∃ level : ℕ, ∃ cell : Set α, ∃ hcell : cell ∈ G.grid.partitions level,
      cell = S ∧ H.cellDeepness G level cell hcell = n)}

lemma HaarSystem.mem_nodesAtDeepness_iff
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n : ℕ) (S : Set α) :
    S ∈ H.nodesAtDeepness G n ↔
      (∃ i : H.Index, i.branchSupport G H = S ∧ i.deepness G H = n) ∨
      (∃ level : ℕ, ∃ cell : Set α, ∃ hcell : cell ∈ G.grid.partitions level,
        cell = S ∧ H.cellDeepness G level cell hcell = n) := by
  rfl

lemma HaarSystem.branchSupport_mem_nodesAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    i.branchSupport G H ∈ H.nodesAtDeepness G (i.deepness G H) := by
  left
  exact ⟨i, rfl, rfl⟩

lemma HaarSystem.exists_parent_node_of_cellDeepness_pos
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} {hcell : cell ∈ G.grid.partitions level}
    (hpos : 0 < H.cellDeepness G level cell hcell) :
    ∃ S ∈ H.nodesAtDeepness G (H.cellDeepness G level cell hcell - 1),
      cell ⊆ S := by
  classical
  cases level with
  | zero =>
      dsimp [HaarSystem.cellDeepness] at hpos
      omega
  | succ level =>
      let parent : Set α := Classical.choose (G.grid.nested level cell hcell)
      have hparent : parent ∈ G.grid.partitions level :=
        (Classical.choose_spec (G.grid.nested level cell hcell)).1
      have hcell_parent : cell ⊆ parent :=
        (Classical.choose_spec (G.grid.nested level cell hcell)).2
      let T := H.binaryRefinement.tree level parent hparent
      have hchild : cell ∈ G.children level parent := ⟨hcell, hcell_parent⟩
      have htop : cell ∈ T.Tops :=
        (H.binaryRefinement.tops_are_children level parent hparent cell).2 hchild
      let parentBranch : Finset (Set α) × Finset (Set α) :=
        Classical.choose (T.TopsareTops cell htop)
      have hparentBranch : parentBranch ∈ T.Branches :=
        (Classical.choose_spec (T.TopsareTops cell htop)).1
      have htop_side : ({cell} : Finset (Set α)) ∈ pairToFinset parentBranch :=
        (Classical.choose_spec (T.TopsareTops cell htop)).2
      let parentIndex : H.Index :=
        { level := level
          cell := parent
          hcell := hparent
          branch := ⟨parentBranch, hparentBranch⟩ }
      refine ⟨parentIndex.branchSupport G H, ?_, ?_⟩
      · have hdeep :
            parentIndex.deepness G H =
              H.cellDeepness G (level + 1) cell hcell - 1 := by
          dsimp [parentIndex, HaarSystem.Index.deepness, HaarSystem.cellDeepness,
            parentBranch, T, hchild, htop]
        rw [← hdeep]
        exact H.branchSupport_mem_nodesAtDeepness G parentIndex
      · have hcell_subset_branch : cell ⊆ haarBranchSupport parentBranch := by
          dsimp [pairToFinset] at htop_side
          have hside :
              ({cell} : Finset (Set α)) = parentBranch.1 ∨
                ({cell} : Finset (Set α)) = parentBranch.2 := by
            simpa [Finset.mem_insert, Finset.mem_singleton] using htop_side
          rcases hside with hleft | hright
          · have hmem : cell ∈ parentBranch.1 := by
              simpa [← hleft]
            exact (subset_branchSupport_of_mem hmem).trans
              (by
                simpa [haarBranchSupport, Combinatorial_Support] using
                  branchSupport_mono (Finset.subset_union_left
                    (s₁ := parentBranch.1) (s₂ := parentBranch.2)))
          · have hmem : cell ∈ parentBranch.2 := by
              simpa [← hright]
            exact (subset_branchSupport_of_mem hmem).trans
              (by
                simpa [haarBranchSupport, Combinatorial_Support] using
                  branchSupport_mono (Finset.subset_union_right
                    (s₁ := parentBranch.1) (s₂ := parentBranch.2)))
        simpa [parentIndex, HaarSystem.Index.branchSupport] using hcell_subset_branch

lemma HaarSystem.cell_mem_nodesAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    {level : ℕ} {cell : Set α} (hcell : cell ∈ G.grid.partitions level) :
    cell ∈ H.nodesAtDeepness G (H.cellDeepness G level cell hcell) := by
  right
  exact ⟨level, cell, hcell, rfl, rfl⟩

lemma HaarSystem.Index.ambient_cell_mem_nodesAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    i.cell ∈ H.nodesAtDeepness G (H.cellDeepness G i.level i.cell i.hcell) := by
  exact H.cell_mem_nodesAtDeepness G i.hcell

lemma HaarSystem.Index.exists_parent_node_of_chainLength_pos
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index)
    (hpos : 0 < chainLength i.branch.2) :
    ∃ S ∈ H.nodesAtDeepness G (i.deepness G H - 1),
      i.branchSupport G H ⊆ S := by
  rcases i.exists_parent_branchSupport_of_chainLength_pos G H hpos with
    ⟨j, hdeep, hsub⟩
  refine ⟨j.branchSupport G H, ?_, hsub⟩
  have hjdeep : j.deepness G H = i.deepness G H - 1 := by
    omega
  rw [← hjdeep]
  exact H.branchSupport_mem_nodesAtDeepness G j

lemma HaarSystem.supportsAtDeepness_subset_nodesAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n : ℕ) :
    H.supportsAtDeepness G n ⊆ H.nodesAtDeepness G n := by
  intro S hS
  rcases hS with ⟨i, rfl, hi⟩
  rw [← hi]
  exact H.branchSupport_mem_nodesAtDeepness G i

lemma HaarSystem.measure_pos_of_mem_nodesAtDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) {n : ℕ} {S : Set α}
    (hS : S ∈ H.nodesAtDeepness G n) :
    0 < G.μ S := by
  rcases hS with hbranch | hcell
  · rcases hbranch with ⟨i, rfl, _hi⟩
    exact i.measure_branchSupport_pos G H
  · rcases hcell with ⟨level, cell, hcell, rfl, _hdeep⟩
    exact G.positive_measure level cell hcell

/-- At deepness zero the induced binary partition consists only of `univ`. -/
theorem HaarSystem.supportsAtDeepness_zero_eq_singleton
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    H.supportsAtDeepness G 0 = {Set.univ} := by
  classical
  ext S
  constructor
  · intro hS
    rcases hS with ⟨i, rfl, hdeep⟩
    rcases i with ⟨level, cell, hcell, branch⟩
    dsimp [HaarSystem.Index.deepness] at hdeep
    have hcellDeep_zero : H.cellDeepness G level cell hcell = 0 := by omega
    have hchain_zero : chainLength branch.2 = 0 := by omega
    have hlevel_zero : level = 0 := by
      cases level with
      | zero => rfl
      | succ level =>
          dsimp [HaarSystem.cellDeepness] at hcellDeep_zero
          omega
    subst level
    have hcell_univ : cell = Set.univ := by
      simpa [G.grid.first_partition_eq_univ] using hcell
    subst cell
    let T := H.binaryRefinement.tree 0 (Set.univ : Set α) hcell
    have hbranch_root : branch.1 = T.Root := by
      have hzero := ChainToRoot_zero branch.2
      have hend := ChainToRoot_end branch.2
      rw [hchain_zero] at hend
      exact hend.symm.trans hzero
    have hsupport :
        haarBranchSupport branch.1 = Set.univ := by
      simpa [T, hbranch_root] using
        (H.haarBranchSupport_root_eq_cell G
          (level := 0) (cell := (Set.univ : Set α)) (hcell := hcell))
    simpa [HaarSystem.Index.branchSupport, hsupport]
  · intro hS
    have hS_univ : S = Set.univ := by simpa using hS
    subst S
    exact ⟨H.rootIndex G, by simp, by simp⟩

theorem HaarSystem.supportsAtDeepness_zero_covers
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    (⋃ S ∈ H.supportsAtDeepness G 0, S) = Set.univ := by
  rw [H.supportsAtDeepness_zero_eq_singleton G]
  ext x
  simp

theorem HaarSystem.supportsAtDeepness_zero_pairwiseDisjoint
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    ∀ A ∈ H.supportsAtDeepness G 0,
      ∀ B ∈ H.supportsAtDeepness G 0, A ≠ B → Disjoint A B := by
  intro A hA B hB hAB
  rw [H.supportsAtDeepness_zero_eq_singleton G] at hA hB
  simp only [Set.mem_singleton_iff] at hA hB
  exact (hAB (hA.trans hB.symm)).elim

theorem HaarSystem.supportsAtDeepness_zero_positive
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    ∀ S ∈ H.supportsAtDeepness G 0, 0 < G.μ S := by
  intro S hS
  exact H.measure_pos_of_mem_supportsAtDeepness G hS

theorem HaarSystem.supportsAtDeepness_one_refines_zero
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    ∀ S ∈ H.supportsAtDeepness G 1,
      ∃ T ∈ H.supportsAtDeepness G 0, S ⊆ T := by
  intro S hS
  refine ⟨Set.univ, ?_, Set.subset_univ S⟩
  rw [H.supportsAtDeepness_zero_eq_singleton G]
  simp

/-- At deepness zero the induced binary grid has the single node `univ`. -/
theorem HaarSystem.nodesAtDeepness_zero_eq_singleton
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    H.nodesAtDeepness G 0 = {Set.univ} := by
  classical
  ext S
  constructor
  · intro hS
    rcases hS with hbranch | hcell
    · rcases hbranch with ⟨i, hiS, hdeep⟩
      have hbranch_zero :
          i.branchSupport G H ∈ H.supportsAtDeepness G 0 :=
        ⟨i, rfl, hdeep⟩
      have h_eq_univ : i.branchSupport G H = Set.univ := by
        have := congrArg (fun A : Set (Set α) => i.branchSupport G H ∈ A)
          (H.supportsAtDeepness_zero_eq_singleton G)
        simp [hbranch_zero] at this
        exact this
      simpa [← hiS, h_eq_univ]
    · rcases hcell with ⟨level, cell, hcell, rfl, hdeep⟩
      have hlevel_zero : level = 0 := by
        cases level with
        | zero => rfl
        | succ level =>
            dsimp [HaarSystem.cellDeepness] at hdeep
            omega
      subst level
      have hcell_univ : cell = Set.univ := by
        simpa [G.grid.first_partition_eq_univ] using hcell
      simpa [hcell_univ]
  · intro hS
    have hS_univ : S = Set.univ := by simpa using hS
    subst S
    left
    exact ⟨H.rootIndex G, by simp, by simp⟩

theorem HaarSystem.nodesAtDeepness_zero_covers
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    (⋃ S ∈ H.nodesAtDeepness G 0, S) = Set.univ := by
  rw [H.nodesAtDeepness_zero_eq_singleton G]
  ext x
  simp

theorem HaarSystem.nodesAtDeepness_zero_pairwiseDisjoint
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    ∀ A ∈ H.nodesAtDeepness G 0,
      ∀ B ∈ H.nodesAtDeepness G 0, A ≠ B → Disjoint A B := by
  intro A hA B hB hAB
  rw [H.nodesAtDeepness_zero_eq_singleton G] at hA hB
  simp only [Set.mem_singleton_iff] at hA hB
  exact (hAB (hA.trans hB.symm)).elim

theorem HaarSystem.nodesAtDeepness_zero_positive
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    ∀ S ∈ H.nodesAtDeepness G 0, 0 < G.μ S := by
  intro S hS
  exact H.measure_pos_of_mem_nodesAtDeepness G hS

theorem HaarSystem.nodesAtDeepness_one_refines_zero
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    ∀ S ∈ H.nodesAtDeepness G 1,
      ∃ T ∈ H.nodesAtDeepness G 0, S ⊆ T := by
  intro S hS
  refine ⟨Set.univ, ?_, Set.subset_univ S⟩
  rw [H.nodesAtDeepness_zero_eq_singleton G]
  simp

/-- Every node at depth `n+1` is contained in a node at depth `n`. -/
theorem HaarSystem.nodesAtDeepness_succ_refines
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n : ℕ) :
    ∀ S ∈ H.nodesAtDeepness G (n + 1),
      ∃ T ∈ H.nodesAtDeepness G n, S ⊆ T := by
  classical
  intro S hS
  rcases hS with hbranch | hcell
  · rcases hbranch with ⟨i, hiS, hideep⟩
    by_cases hpos : 0 < chainLength i.branch.2
    · rcases i.exists_parent_node_of_chainLength_pos G H hpos with ⟨T, hT, hsub⟩
      refine ⟨T, ?_, ?_⟩
      · have hn : i.deepness G H - 1 = n := by omega
        simpa [hn, hideep] using hT
      · simpa [← hiS] using hsub
    · have hzero : chainLength i.branch.2 = 0 := by omega
      have hcellDeep : H.cellDeepness G i.level i.cell i.hcell = n + 1 := by
        dsimp [HaarSystem.Index.deepness] at hideep
        omega
      have hcell_pos : 0 < H.cellDeepness G i.level i.cell i.hcell := by omega
      rcases H.exists_parent_node_of_cellDeepness_pos G hcell_pos with ⟨T, hT, hsub_cell⟩
      refine ⟨T, ?_, ?_⟩
      · have hn : H.cellDeepness G i.level i.cell i.hcell - 1 = n := by omega
        simpa [hn] using hT
      · have hS_cell : S = i.cell := by
          rw [← hiS]
          exact i.branchSupport_eq_cell_of_chainLength_zero G H hzero
        simpa [hS_cell] using hsub_cell
  · rcases hcell with ⟨level, cell, hcell, hS_cell, hdeep⟩
    have hcell_pos : 0 < H.cellDeepness G level cell hcell := by omega
    rcases H.exists_parent_node_of_cellDeepness_pos G hcell_pos with ⟨T, hT, hsub⟩
    refine ⟨T, ?_, ?_⟩
    · have hn : H.cellDeepness G level cell hcell - 1 = n := by omega
      simpa [hn] using hT
    · simpa [← hS_cell] using hsub

theorem HaarSystem.nodesAtDeepness_add_refines
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n k : ℕ) :
    ∀ S ∈ H.nodesAtDeepness G (n + k),
      ∃ T ∈ H.nodesAtDeepness G n, S ⊆ T := by
  induction k generalizing n with
  | zero =>
      intro S hS
      refine ⟨S, ?_, Set.Subset.rfl⟩
      simpa using hS
  | succ k ih =>
      intro S hS
      have hS_succ : S ∈ H.nodesAtDeepness G ((n + k) + 1) := by
        simpa [Nat.add_assoc] using hS
      rcases H.nodesAtDeepness_succ_refines G (n + k) S hS_succ with
        ⟨U, hU, hSU⟩
      rcases ih n U hU with ⟨T, hT, hUT⟩
      exact ⟨T, hT, hSU.trans hUT⟩

theorem HaarSystem.nodesAtDeepness_refines_of_le
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) {n m : ℕ} (hnm : n ≤ m) :
    ∀ S ∈ H.nodesAtDeepness G m,
      ∃ T ∈ H.nodesAtDeepness G n, S ⊆ T := by
  intro S hS
  have hm : m = n + (m - n) := (Nat.add_sub_of_le hnm).symm
  have hS' : S ∈ H.nodesAtDeepness G (n + (m - n)) := by
    simpa [← hm] using hS
  exact H.nodesAtDeepness_add_refines G n (m - n) S hS'

/-- A choice-based deepness for an element of the set of all Haar branch supports.

The canonical object carrying the branch information is `HaarSystem.Index`; this definition is
useful when one has only a support set known to lie in `H.branchSupports G`. It chooses one global
branch index realizing that support and returns its index deepness. -/
noncomputable def HaarSystem.supportDeepness
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (S : {S : Set α // S ∈ H.branchSupports G}) : ℕ :=
  (Classical.choose S.2).deepness G H

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

/-- Estrutura da sequência de partições induzidas pelos suportes dos ramos do sistema de Haar.
    - A partição de nível zero é {univ}.
    - Nós de mesma profundidade são iguais ou disjuntos.
    - Todo elemento da partição tem exatamente dois filhos na próxima partição.
    - Se S = supp(A,B), então os filhos de S são supp A e supp B.
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
    (∃! (A B : Set α),
      A ≠ B ∧
      A ∈ H.nodesAtDeepness G (n + 1) ∧
      B ∈ H.nodesAtDeepness G (n + 1) ∧
      A ⊆ S ∧ B ⊆ S ∧
      S = A ∪ B ∧ Disjoint A B)) ∧
  (∀ n S A B,
    S ∈ H.nodesAtDeepness G n →
    ∃ (i : H.Index), i.branchSupport G H = S ∧
      ∃ (p : Finset (Set α) × Finset (Set α)),
        p ∈ (H.binaryRefinement.tree i.level i.cell i.hcell).Branches ∧
        S = haarBranchSupport p ∧
        A = haarBranchSupport p.1 ∧ B = haarBranchSupport p.2 →
        A ∈ H.nodesAtDeepness G (n + 1) ∧ B ∈ H.nodesAtDeepness G (n + 1) ∧
        S = A ∪ B ∧ Disjoint A B) ∧
  (∀ level cell (hcell : cell ∈ G.grid.partitions level)
      (p : Finset (Set α) × Finset (Set α)),
      p ∈ (H.binaryRefinement.tree level cell hcell).Branches →
      ∃ n, haarBranchSupport p ∈ H.nodesAtDeepness G n) := by
  constructor
  · exact H.nodesAtDeepness_zero_eq_singleton G
  constructor
  · intro n S₁ S₂ hS₁ hS₂
    sorry
  constructor
  · intro n S hS
    sorry
  constructor
  · intro n S A B hS
    sorry
  · intro level cell hcell p hp
    refine ⟨(HaarSystem.Index.deepness G H
      ({ level := level, cell := cell, hcell := hcell, branch := ⟨p, hp⟩ } : H.Index)), ?_⟩
    exact H.branchSupport_mem_nodesAtDeepness G
      ({ level := level, cell := cell, hcell := hcell, branch := ⟨p, hp⟩ } : H.Index)

end UnbalancedHaarWavelet
