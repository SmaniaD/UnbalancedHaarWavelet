import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import UnbalancedHaarWavelet.GridDefinition
import UnbalancedHaarWavelet.HaarWaveletsDefinition

/-!
Orthogonality and energy facts for Haar wavelets.

This file proves integrability, zero-mean properties, and pairwise
orthogonality statements, first for local branch supports and then for global
indices in a Haar system.
-/







namespace UnbalancedHaarWavelet

variable {α : Type*} [MeasurableSpace α]

/-- A Haar wavelet is integrable when its two supports are measurable and the measure is finite. -/
lemma integrable_haarWavelet
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (A B : Set α) (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B) :
    MeasureTheory.Integrable (haarWavelet μ A B) μ := by
  have hIntA :
      MeasureTheory.Integrable
        (fun x => Set.indicator A (fun _ => 1 / (μ A).toReal) x) μ :=
    (MeasureTheory.integrable_const (1 / (μ A).toReal)).indicator hA_meas
  have hIntB :
      MeasureTheory.Integrable
        (fun x => Set.indicator B (fun _ => 1 / (μ B).toReal) x) μ :=
    (MeasureTheory.integrable_const (1 / (μ B).toReal)).indicator hB_meas
  change MeasureTheory.Integrable
    (fun x =>
      Set.indicator A (fun _ => 1 / (μ A).toReal) x -
        Set.indicator B (fun _ => 1 / (μ B).toReal) x) μ
  exact hIntA.sub hIntB

/-- Uniform pointwise bound for a Haar wavelet. -/
lemma norm_haarWavelet_le
    (μ : MeasureTheory.Measure α) (A B : Set α) (x : α) :
    ‖haarWavelet μ A B x‖ ≤
      ‖(1 / (μ A).toReal : ℝ)‖ + ‖(1 / (μ B).toReal : ℝ)‖ := by
  calc
    ‖haarWavelet μ A B x‖ =
        ‖Set.indicator A (fun _ => 1 / (μ A).toReal) x -
          Set.indicator B (fun _ => 1 / (μ B).toReal) x‖ := by
          rfl
    _ ≤ ‖Set.indicator A (fun _ => 1 / (μ A).toReal) x‖ +
        ‖Set.indicator B (fun _ => 1 / (μ B).toReal) x‖ :=
          norm_sub_le _ _
    _ ≤ ‖(1 / (μ A).toReal : ℝ)‖ + ‖(1 / (μ B).toReal : ℝ)‖ := by
          exact add_le_add
            (norm_indicator_le_norm_self (s := A) (fun _ : α => (1 / (μ A).toReal : ℝ)) x)
            (norm_indicator_le_norm_self (s := B) (fun _ : α => (1 / (μ B).toReal : ℝ)) x)

/-- The product of two Haar wavelets is integrable when all four supports are measurable. -/
lemma integrable_haarWavelet_mul_haarWavelet
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (A B C D : Set α)
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (hC_meas : MeasurableSet C) (hD_meas : MeasurableSet D) :
    MeasureTheory.Integrable
      (fun x => haarWavelet μ A B x * haarWavelet μ C D x) μ := by
  have hAB_int := integrable_haarWavelet μ A B hA_meas hB_meas
  have hCD_int := integrable_haarWavelet μ C D hC_meas hD_meas
  exact hAB_int.mul_bdd
    hCD_int.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_haarWavelet_le μ C D))

/-- The square integral of one Haar wavelet. -/
theorem integral_haarWavelet_mul_self_eq
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (A B : Set α)
    (hAB : Disjoint A B)
    (hA_meas : MeasurableSet A)
    (hB_meas : MeasurableSet B)
    (hA_pos : 0 < μ A)
    (hB_pos : 0 < μ B) :
    ∫ x, haarWavelet μ A B x * haarWavelet μ A B x ∂μ =
      1 / (μ A).toReal + 1 / (μ B).toReal := by
  let μA : ℝ := (μ A).toReal
  let μB : ℝ := (μ B).toReal
  have hμA_ne : μA ≠ 0 := by
    dsimp [μA]
    exact ne_of_gt
      (ENNReal.toReal_pos (ne_of_gt hA_pos) (MeasureTheory.measure_lt_top (μ := μ) A).ne)
  have hμB_ne : μB ≠ 0 := by
    dsimp [μB]
    exact ne_of_gt
      (ENNReal.toReal_pos (ne_of_gt hB_pos) (MeasureTheory.measure_lt_top (μ := μ) B).ne)
  have hIntA :
      MeasureTheory.Integrable
        (fun y => Set.indicator A (fun _ => (1 / μA) * (1 / μA)) y) μ :=
    (MeasureTheory.integrable_const ((1 / μA) * (1 / μA))).indicator hA_meas
  have hIntB :
      MeasureTheory.Integrable
        (fun y => Set.indicator B (fun _ => (1 / μB) * (1 / μB)) y) μ :=
    (MeasureTheory.integrable_const ((1 / μB) * (1 / μB))).indicator hB_meas
  have hfun :
      (fun y => haarWavelet μ A B y * haarWavelet μ A B y) =
        fun y => Set.indicator A (fun _ => (1 / μA) * (1 / μA)) y +
          Set.indicator B (fun _ => (1 / μB) * (1 / μB)) y := by
    funext y
    by_cases hyA : y ∈ A
    · have hyB : y ∉ B := by
        intro hyB
        exact (Set.disjoint_left.mp hAB hyA hyB).elim
      simp [haarWavelet, μA, μB, hyA, hyB]
    · by_cases hyB : y ∈ B
      · simp [haarWavelet, μA, μB, hyA, hyB]
      · simp [haarWavelet, μA, μB, hyA, hyB]
  rw [hfun, MeasureTheory.integral_add hIntA hIntB]
  rw [MeasureTheory.integral_indicator hA_meas, MeasureTheory.integral_indicator hB_meas]
  rw [MeasureTheory.setIntegral_const, MeasureTheory.setIntegral_const]
  rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
  change (μ A).toReal * ((1 / μA) * (1 / μA)) +
      (μ B).toReal * ((1 / μB) * (1 / μB)) =
    1 / (μ A).toReal + 1 / (μ B).toReal
  rw [show (μ A).toReal = μA by rfl, show (μ B).toReal = μB by rfl]
  simp [div_eq_mul_inv]
  field_simp [hμA_ne, hμB_ne]

/-- Orthogonality of two Haar wavelets when the four supports are pairwise disjoint
across the two wavelets. -/
theorem integral_mul_haarWavelet_eq_zero_of_disjoint
    (μ : MeasureTheory.Measure α)
    (A B C D : Set α)
    (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hBC : Disjoint B C)
    (hBD : Disjoint B D) :
    ∫ x, haarWavelet μ A B x * haarWavelet μ C D x ∂ μ = 0 := by
  have hAC' := Set.disjoint_left.mp hAC
  have hAD' := Set.disjoint_left.mp hAD
  have hBC' := Set.disjoint_left.mp hBC
  have hBD' := Set.disjoint_left.mp hBD
  have hpointwise :
      ∀ x,
        haarWavelet μ A B x * haarWavelet μ C D x = 0 := by
    intro x
    set iA : ℝ :=
      Set.indicator A
        (fun _ => 1 / (μ A).toReal) x
    set iB : ℝ :=
      Set.indicator B
        (fun _ => 1 / (μ B).toReal) x
    set iC : ℝ :=
      Set.indicator C
        (fun _ => 1 / (μ C).toReal) x
    set iD : ℝ :=
      Set.indicator D
        (fun _ => 1 / (μ D).toReal) x
    have hiAC : iA * iC = 0 := by
      by_cases hxA : x ∈ A
      · have hxC : x ∉ C := by
          intro hxC
          exact (hAC' hxA hxC).elim
        simp [iA, iC, hxA, hxC]
      · simp [iA, hxA]
    have hiAD : iA * iD = 0 := by
      by_cases hxA : x ∈ A
      · have hxD : x ∉ D := by
          intro hxD
          exact (hAD' hxA hxD).elim
        simp [iA, iD, hxA, hxD]
      · simp [iA, hxA]
    have hiBC : iB * iC = 0 := by
      by_cases hxB : x ∈ B
      · have hxC : x ∉ C := by
          intro hxC
          exact (hBC' hxB hxC).elim
        simp [iB, iC, hxB, hxC]
      · simp [iB, hxB]
    have hiBD : iB * iD = 0 := by
      by_cases hxB : x ∈ B
      · have hxD : x ∉ D := by
          intro hxD
          exact (hBD' hxB hxD).elim
        simp [iB, iD, hxB, hxD]
      · simp [iB, hxB]
    calc
      haarWavelet μ A B x * haarWavelet μ C D x
          = (iA - iB) * (iC - iD) := by simp [haarWavelet, iA, iB, iC, iD]
      _ = iA * iC - iA * iD - iB * iC + iB * iD := by ring
      _ = 0 := by simp [hiAC, hiAD, hiBC, hiBD]
  have hfun :
      (fun x => haarWavelet μ A B x * haarWavelet μ C D x)
        = fun _ => (0 : ℝ) := by
    funext x
    exact hpointwise x
  rw [hfun]
  simp

/-- The Haar wavelet `ψ_{A,B}` has zero mean under positivity assumptions. -/
theorem integral_haarWavelet_eq_zero_of_pos
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (A B : Set α)
    (hAB : Disjoint A B)
    (hA_meas : MeasurableSet A)
    (hB_meas : MeasurableSet B)
    (hA_pos : 0 < μ A)
    (hB_pos : 0 < μ B) :
    ∫ x, haarWavelet μ A B x ∂μ = 0 := by
  let _ := hAB
  have hA_ne_zero : μ A ≠ 0 := ne_of_gt hA_pos
  have hB_ne_zero : μ B ≠ 0 := ne_of_gt hB_pos
  have hA_lt_top : μ A < ⊤ :=
    MeasureTheory.measure_lt_top (μ := μ) A
  have hB_lt_top : μ B < ⊤ :=
    MeasureTheory.measure_lt_top (μ := μ) B
  have hA_toReal_ne_zero : (μ A).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hA_ne_zero hA_lt_top.ne)
  have hB_toReal_ne_zero : (μ B).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hB_ne_zero hB_lt_top.ne)
  have hIntA :
      MeasureTheory.Integrable
        (fun x =>
          Set.indicator A
            (fun _ => 1 / (μ A).toReal) x) μ := by
    exact (MeasureTheory.integrable_const
      (1 / (μ A).toReal)).indicator hA_meas
  have hIntB :
      MeasureTheory.Integrable
        (fun x =>
          Set.indicator B
            (fun _ => 1 / (μ B).toReal) x) μ := by
    exact (MeasureTheory.integrable_const
      (1 / (μ B).toReal)).indicator hB_meas
  calc
    ∫ x, haarWavelet μ A B x ∂μ
        = ∫ x,
            Set.indicator A
              (fun _ => 1 / (μ A).toReal) x
            -
            Set.indicator B
              (fun _ => 1 / (μ B).toReal) x ∂μ := by
          simp [haarWavelet]
    _ =
        (∫ x,
          Set.indicator A
            (fun _ => 1 / (μ A).toReal) x ∂μ)
        -
        (∫ x,
          Set.indicator B
            (fun _ => 1 / (μ B).toReal) x ∂μ) := by
          exact MeasureTheory.integral_sub hIntA hIntB
    _ =
        μ.real A * (μ A).toReal⁻¹
        -
        (μ.real B * (μ B).toReal⁻¹) := by
      simp [hA_meas, hB_meas]
    _ = 1 - 1 := by
      change
        (μ A).toReal * (μ A).toReal⁻¹
          -
          ((μ B).toReal * (μ B).toReal⁻¹)
          = 1 - 1
      field_simp [hA_toReal_ne_zero, hB_toReal_ne_zero]
    _ = 0 := by ring



/-- Orthogonality when `S_A ∪ S_B ⊆ S_C`, `S_C ⟂ S_D`, and `ψ_{A,B}` has zero mean. -/
theorem integral_mul_haarWavelet_eq_zero_of_subset_left
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (A B C D : Set α)
    (hAB : Disjoint A B)
    (hCD : Disjoint C D)
    (hsub : A ∪ B ⊆ C)
    (hA_meas : MeasurableSet A)
    (hB_meas : MeasurableSet B)
    (hA_pos : 0 < μ A)
    (hB_pos : 0 < μ B)
    :
    ∫ x, haarWavelet μ A B x * haarWavelet μ C D x ∂ μ = 0 := by
  have hmean_zero : ∫ x, haarWavelet μ A B x ∂μ = 0 := by
    exact integral_haarWavelet_eq_zero_of_pos
      μ A B hAB hA_meas hB_meas hA_pos hB_pos
  let cC : ℝ := 1 / (μ C).toReal
  have hCD' := Set.disjoint_left.mp hCD
  let _ := hAB
  have hmul_eq :
      (fun x => haarWavelet μ A B x * haarWavelet μ C D x)
        = fun x => cC * haarWavelet μ A B x := by
    funext x
    by_cases hxU : x ∈ A ∪ B
    · have hxC : x ∈ C := hsub hxU
      have hxD : x ∉ D := by
        intro hxD
        exact (hCD' hxC hxD).elim
      simp [haarWavelet, cC, hxC, hxD, mul_comm]
    · have hxA : x ∉ A := by
        intro hxA
        exact hxU (Or.inl hxA)
      have hxB : x ∉ B := by
        intro hxB
        exact hxU (Or.inr hxB)
      simp [haarWavelet, hxA, hxB]
  rw [hmul_eq, MeasureTheory.integral_const_mul, hmean_zero]
  simp

/-- Orthogonality when `S_A ∪ S_B ⊆ S_D`, `S_C ⟂ S_D`, and `ψ_{A,B}` has zero mean.
This is the symmetric containment case to `integral_mul_haarWavelet_eq_zero_of_subset_left`. -/
theorem integral_mul_haarWavelet_eq_zero_of_subset_right
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ]
    (A B C D : Set α)
    (hAB : Disjoint A B)
    (hCD : Disjoint C D)
  (hsub : A ∪ B ⊆ D)
  (hC_meas : MeasurableSet C)
    (hA_meas : MeasurableSet A)
    (hB_meas : MeasurableSet B)
    (hA_pos : 0 < μ A)
    (hB_pos : 0 < μ B) :
    ∫ x, haarWavelet μ A B x * haarWavelet μ C D x ∂ μ = 0 := by
  have hmean_zero : ∫ x, haarWavelet μ A B x ∂μ = 0 := by
    exact integral_haarWavelet_eq_zero_of_pos
      μ A B hAB hA_meas hB_meas hA_pos hB_pos
  let cD : ℝ := 1 / (μ D).toReal
  have hCD' := Set.disjoint_left.mp hCD
  let _ := hAB
  let _ := hC_meas
  have hmul_eq :
      (fun x => haarWavelet μ A B x * haarWavelet μ C D x)
        = fun x => (-cD) * haarWavelet μ A B x := by
    funext x
    by_cases hxU : x ∈ A ∪ B
    · have hxD : x ∈ D := hsub hxU
      have hxC : x ∉ C := by
        intro hxC
        exact (hCD' hxC hxD).elim
      simp [haarWavelet, cD, hxD, hxC, mul_comm]
    · have hxA : x ∉ A := by
        intro hxA
        exact hxU (Or.inl hxA)
      have hxB : x ∉ B := by
        intro hxB
        exact hxU (Or.inr hxB)
      simp [haarWavelet, hxA, hxB]
  rw [hmul_eq, MeasureTheory.integral_const_mul, hmean_zero]
  simp

/-- Orthogonality in `L²(μ)` for two distinct Haar wavelets in the same Haar system,
assuming the usual support relation (disjointness or inclusion) and positivity/measurability
for the first wavelet. -/
theorem HaarSystem.integral_mul_haarWavelets_eq_zero_of_distinct_core
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (n : ℕ) (Q : Set α) (hQ : Q ∈ G.grid.partitions n)
    (p q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches})
    (hpq : p ≠ q)
    (hAB : Disjoint (branchSupport p.1.1) (branchSupport p.1.2))
    (hCD : Disjoint (branchSupport q.1.1) (branchSupport q.1.2))
    (hC_meas : MeasurableSet (branchSupport q.1.1))
    (hA_meas : MeasurableSet (branchSupport p.1.1))
    (hB_meas : MeasurableSet (branchSupport p.1.2))
    (hA_pos : 0 < G.μ (branchSupport p.1.1))
    (hB_pos : 0 < G.μ (branchSupport p.1.2))
    (hrel :
      Disjoint
        (branchSupport p.1.1 ∪ branchSupport p.1.2)
        (branchSupport q.1.1 ∪ branchSupport q.1.2)
      ∨ branchSupport p.1.1 ∪ branchSupport p.1.2 ⊆ branchSupport q.1.1
      ∨ branchSupport p.1.1 ∪ branchSupport p.1.2 ⊆ branchSupport q.1.2) :
    ∫ x, H.haarWavelets n Q hQ p x * H.haarWavelets n Q hQ q x ∂ G.μ = 0 := by
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  let _ := hpq
  rw [H.haarWavelets_def, H.haarWavelets_def]
  rcases hrel with hdisj | hsub_left | hsub_right
  · have hAC : Disjoint (branchSupport p.1.1) (branchSupport q.1.1) :=
      (hdisj.mono_left Set.subset_union_left).mono_right Set.subset_union_left
    have hAD : Disjoint (branchSupport p.1.1) (branchSupport q.1.2) :=
      (hdisj.mono_left Set.subset_union_left).mono_right Set.subset_union_right
    have hBC : Disjoint (branchSupport p.1.2) (branchSupport q.1.1) :=
      (hdisj.mono_left Set.subset_union_right).mono_right Set.subset_union_left
    have hBD : Disjoint (branchSupport p.1.2) (branchSupport q.1.2) :=
      (hdisj.mono_left Set.subset_union_right).mono_right Set.subset_union_right
    exact integral_mul_haarWavelet_eq_zero_of_disjoint
      G.μ (branchSupport p.1.1) (branchSupport p.1.2)
      (branchSupport q.1.1) (branchSupport q.1.2)
      hAC hAD hBC hBD
  · exact integral_mul_haarWavelet_eq_zero_of_subset_left
      G.μ
      (branchSupport p.1.1) (branchSupport p.1.2)
      (branchSupport q.1.1) (branchSupport q.1.2)
      hAB hCD hsub_left hA_meas hB_meas hA_pos hB_pos
  · exact integral_mul_haarWavelet_eq_zero_of_subset_right
      G.μ
      (branchSupport p.1.1) (branchSupport p.1.2)
      (branchSupport q.1.1) (branchSupport q.1.2)
      hAB hCD hsub_right hC_meas
      hA_meas hB_meas hA_pos hB_pos

/-- Orthogonality in `L²(μ)` for two distinct Haar wavelets in the same Haar system,
with the support relation automatically derived from the tree `SupportProperty`. -/
theorem HaarSystem.integral_mul_haarWavelets_eq_zero_of_distinct
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (n : ℕ) (Q : Set α) (hQ : Q ∈ G.grid.partitions n)
    (p q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches})
    (hpq : p ≠ q) :
    ∫ x, H.haarWavelets n Q hQ p x * H.haarWavelets n Q hQ q x ∂ G.μ = 0 := by
  let T := H.binaryRefinement.tree n Q hQ
  have hpq_val : p.1 ≠ q.1 := by
    intro h
    exact hpq (Subtype.ext h)
  have hp_childs : p.1.1 ⊆ T.Childs ∧ p.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds p.1 p.2
  have hq_childs : q.1.1 ⊆ T.Childs ∧ q.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds q.1 q.2
  have hp1_part : ∀ s, s ∈ p.1.1 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    have hs_child : s ∈ T.Childs := hp_childs.1 hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child |>.1
  have hp2_part : ∀ s, s ∈ p.1.2 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    have hs_child : s ∈ T.Childs := hp_childs.2 hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child |>.1
  have hq1_part : ∀ s, s ∈ q.1.1 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    have hs_child : s ∈ T.Childs := hq_childs.1 hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child |>.1
  have hq2_part : ∀ s, s ∈ q.1.2 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    have hs_child : s ∈ T.Childs := hq_childs.2 hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child |>.1
  have hp_nonempty : p.1.1.Nonempty ∧ p.1.2.Nonempty := T.NonemptyPairs p.1 p.2
  have hq_nonempty : q.1.1.Nonempty ∧ q.1.2.Nonempty := T.NonemptyPairs q.1 q.2
  have hAB_cells : Disjoint p.1.1 p.1.2 := T.DisjointComponents p.1 p.2
  have hCD_cells : Disjoint q.1.1 q.1.2 := T.DisjointComponents q.1 q.2
  have hp1_pos_cells : ∀ s, s ∈ p.1.1 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (n + 1) s (hp1_part s hs)
  have hp2_pos_cells : ∀ s, s ∈ p.1.2 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (n + 1) s (hp2_part s hs)
  have hq1_pos_cells : ∀ s, s ∈ q.1.1 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (n + 1) s (hq1_part s hs)
  have hq2_pos_cells : ∀ s, s ∈ q.1.2 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (n + 1) s (hq2_part s hs)
  have hAB : Disjoint (branchSupport p.1.1) (branchSupport p.1.2) :=
    disjoint_branchSupport_of_finset_disjoint G n p.1.1 p.1.2 hp1_part hp2_part hAB_cells
  have hCD : Disjoint (branchSupport q.1.1) (branchSupport q.1.2) :=
    disjoint_branchSupport_of_finset_disjoint G n q.1.1 q.1.2 hq1_part hq2_part hCD_cells
  have hA_meas : MeasurableSet (branchSupport p.1.1) :=
    measurableSet_branchSupport_of_partition G n p.1.1 hp1_part
  have hB_meas : MeasurableSet (branchSupport p.1.2) :=
    measurableSet_branchSupport_of_partition G n p.1.2 hp2_part
  have hC_meas : MeasurableSet (branchSupport q.1.1) :=
    measurableSet_branchSupport_of_partition G n q.1.1 hq1_part
  have hD_meas : MeasurableSet (branchSupport q.1.2) :=
    measurableSet_branchSupport_of_partition G n q.1.2 hq2_part
  have hA_pos : 0 < G.μ (branchSupport p.1.1) :=
    measure_branchSupport_pos_of_nonempty G p.1.1 hp1_pos_cells hp_nonempty.1
  have hB_pos : 0 < G.μ (branchSupport p.1.2) :=
    measure_branchSupport_pos_of_nonempty G p.1.2 hp2_pos_cells hp_nonempty.2
  have hC_pos : 0 < G.μ (branchSupport q.1.1) :=
    measure_branchSupport_pos_of_nonempty G q.1.1 hq1_pos_cells hq_nonempty.1
  have hD_pos : 0 < G.μ (branchSupport q.1.2) :=
    measure_branchSupport_pos_of_nonempty G q.1.2 hq2_pos_cells hq_nonempty.2
  have hsupport := T.SupportProperty p.1 p.2 q.1 q.2 hpq_val
  rcases hsupport with hdisjCells | hpSubq1 | hpSubq2 | hqSubp1 | hqSubp2
  · have hAC_cells : Disjoint p.1.1 q.1.1 := by
      refine Finset.disjoint_left.2 ?_
      intro s hsA hsC
      exact (Finset.disjoint_left.mp hdisjCells)
        (Finset.mem_union.mpr (Or.inl hsA))
        (Finset.mem_union.mpr (Or.inl hsC))
    have hAD_cells : Disjoint p.1.1 q.1.2 := by
      refine Finset.disjoint_left.2 ?_
      intro s hsA hsD
      exact (Finset.disjoint_left.mp hdisjCells)
        (Finset.mem_union.mpr (Or.inl hsA))
        (Finset.mem_union.mpr (Or.inr hsD))
    have hBC_cells : Disjoint p.1.2 q.1.1 := by
      refine Finset.disjoint_left.2 ?_
      intro s hsB hsC
      exact (Finset.disjoint_left.mp hdisjCells)
        (Finset.mem_union.mpr (Or.inr hsB))
        (Finset.mem_union.mpr (Or.inl hsC))
    have hBD_cells : Disjoint p.1.2 q.1.2 := by
      refine Finset.disjoint_left.2 ?_
      intro s hsB hsD
      exact (Finset.disjoint_left.mp hdisjCells)
        (Finset.mem_union.mpr (Or.inr hsB))
        (Finset.mem_union.mpr (Or.inr hsD))
    have hAC : Disjoint (branchSupport p.1.1) (branchSupport q.1.1) :=
      disjoint_branchSupport_of_finset_disjoint G n p.1.1 q.1.1 hp1_part hq1_part hAC_cells
    have hAD : Disjoint (branchSupport p.1.1) (branchSupport q.1.2) :=
      disjoint_branchSupport_of_finset_disjoint G n p.1.1 q.1.2 hp1_part hq2_part hAD_cells
    have hBC : Disjoint (branchSupport p.1.2) (branchSupport q.1.1) :=
      disjoint_branchSupport_of_finset_disjoint G n p.1.2 q.1.1 hp2_part hq1_part hBC_cells
    have hBD : Disjoint (branchSupport p.1.2) (branchSupport q.1.2) :=
      disjoint_branchSupport_of_finset_disjoint G n p.1.2 q.1.2 hp2_part hq2_part hBD_cells
    rw [H.haarWavelets_def, H.haarWavelets_def]
    exact integral_mul_haarWavelet_eq_zero_of_disjoint
      G.μ (branchSupport p.1.1) (branchSupport p.1.2)
      (branchSupport q.1.1) (branchSupport q.1.2)
      hAC hAD hBC hBD
  · have hp1_sub_q1 : p.1.1 ⊆ q.1.1 := by
      intro s hs
      exact hpSubq1 (Finset.mem_union.mpr (Or.inl hs))
    have hp2_sub_q1 : p.1.2 ⊆ q.1.1 := by
      intro s hs
      exact hpSubq1 (Finset.mem_union.mpr (Or.inr hs))
    have hsub : branchSupport p.1.1 ∪ branchSupport p.1.2 ⊆ branchSupport q.1.1 :=
      Set.union_subset (branchSupport_mono hp1_sub_q1) (branchSupport_mono hp2_sub_q1)
    exact HaarSystem.integral_mul_haarWavelets_eq_zero_of_distinct_core
      G H n Q hQ p q hpq hAB hCD hC_meas hA_meas hB_meas hA_pos hB_pos
      (Or.inr (Or.inl hsub))
  · have hp1_sub_q2 : p.1.1 ⊆ q.1.2 := by
      intro s hs
      exact hpSubq2 (Finset.mem_union.mpr (Or.inl hs))
    have hp2_sub_q2 : p.1.2 ⊆ q.1.2 := by
      intro s hs
      exact hpSubq2 (Finset.mem_union.mpr (Or.inr hs))
    have hsub : branchSupport p.1.1 ∪ branchSupport p.1.2 ⊆ branchSupport q.1.2 :=
      Set.union_subset (branchSupport_mono hp1_sub_q2) (branchSupport_mono hp2_sub_q2)
    exact HaarSystem.integral_mul_haarWavelets_eq_zero_of_distinct_core
      G H n Q hQ p q hpq hAB hCD hC_meas hA_meas hB_meas hA_pos hB_pos
      (Or.inr (Or.inr hsub))
  · have hq1_sub_p1 : q.1.1 ⊆ p.1.1 := by
      intro s hs
      exact hqSubp1 (Finset.mem_union.mpr (Or.inl hs))
    have hq2_sub_p1 : q.1.2 ⊆ p.1.1 := by
      intro s hs
      exact hqSubp1 (Finset.mem_union.mpr (Or.inr hs))
    have hsub_swap : branchSupport q.1.1 ∪ branchSupport q.1.2 ⊆ branchSupport p.1.1 :=
      Set.union_subset (branchSupport_mono hq1_sub_p1) (branchSupport_mono hq2_sub_p1)
    have hswap :
        ∫ x, H.haarWavelets n Q hQ q x * H.haarWavelets n Q hQ p x ∂ G.μ = 0 :=
      HaarSystem.integral_mul_haarWavelets_eq_zero_of_distinct_core
        G H n Q hQ q p (by simpa [ne_eq] using hpq.symm)
        hCD hAB hA_meas hC_meas hD_meas hC_pos hD_pos
        (Or.inr (Or.inl hsub_swap))
    have hmul_comm :
        (fun x => H.haarWavelets n Q hQ p x * H.haarWavelets n Q hQ q x)
          = (fun x => H.haarWavelets n Q hQ q x * H.haarWavelets n Q hQ p x) := by
      funext x
      rw [mul_comm]
    rw [hmul_comm]
    exact hswap
  · have hq1_sub_p2 : q.1.1 ⊆ p.1.2 := by
      intro s hs
      exact hqSubp2 (Finset.mem_union.mpr (Or.inl hs))
    have hq2_sub_p2 : q.1.2 ⊆ p.1.2 := by
      intro s hs
      exact hqSubp2 (Finset.mem_union.mpr (Or.inr hs))
    have hsub_swap : branchSupport q.1.1 ∪ branchSupport q.1.2 ⊆ branchSupport p.1.2 :=
      Set.union_subset (branchSupport_mono hq1_sub_p2) (branchSupport_mono hq2_sub_p2)
    have hswap :
        ∫ x, H.haarWavelets n Q hQ q x * H.haarWavelets n Q hQ p x ∂ G.μ = 0 :=
      HaarSystem.integral_mul_haarWavelets_eq_zero_of_distinct_core
        G H n Q hQ q p (by simpa [ne_eq] using hpq.symm)
        hCD hAB hA_meas hC_meas hD_meas hC_pos hD_pos
        (Or.inr (Or.inr hsub_swap))
    have hmul_comm :
        (fun x => H.haarWavelets n Q hQ p x * H.haarWavelets n Q hQ q x)
          = (fun x => H.haarWavelets n Q hQ q x * H.haarWavelets n Q hQ p x) := by
      funext x
      rw [mul_comm]
    rw [hmul_comm]
    exact hswap

/-- Haar wavelets attached to two different cells at the same partition level are orthogonal,
because their supports lie in disjoint partition cells. -/
theorem HaarSystem.integral_mul_haarWavelets_eq_zero_of_distinct_distinct_Q
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (n : ℕ)
    (Q : Set α)
    (hQ : Q ∈ G.grid.partitions n)
    (P : Set α)
    (hP : P ∈ G.grid.partitions n)
    (q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches})
    (p : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n P hP).Branches})
    (hPQ : P ≠ Q) :
    ∫ x, H.haarWavelets n Q hQ q x * H.haarWavelets n P hP p x ∂ G.μ = 0 := by
  let TP := H.binaryRefinement.tree n P hP
  let TQ := H.binaryRefinement.tree n Q hQ
  have hQP_disj : Disjoint Q P := (G.grid.disjoint n P Q hP hQ hPQ).symm
  have hp_childs : p.1.1 ⊆ TP.Childs ∧ p.1.2 ⊆ TP.Childs :=
    TP.TreeStructureChilds p.1 p.2
  have hq_childs : q.1.1 ⊆ TQ.Childs ∧ q.1.2 ⊆ TQ.Childs :=
    TQ.TreeStructureChilds q.1 q.2
  have hp1_sub_P : branchSupport p.1.1 ⊆ P := by
    intro x hx
    rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
    have hs_child : s ∈ TP.Childs := hp_childs.1 hs
    have hs_children : s ∈ G.children n P :=
      (H.binaryRefinement.childs_are_children n P hP s).1 hs_child
    exact hs_children.2 hxs
  have hp2_sub_P : branchSupport p.1.2 ⊆ P := by
    intro x hx
    rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
    have hs_child : s ∈ TP.Childs := hp_childs.2 hs
    have hs_children : s ∈ G.children n P :=
      (H.binaryRefinement.childs_are_children n P hP s).1 hs_child
    exact hs_children.2 hxs
  have hq1_sub_Q : branchSupport q.1.1 ⊆ Q := by
    intro x hx
    rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
    have hs_child : s ∈ TQ.Childs := hq_childs.1 hs
    have hs_children : s ∈ G.children n Q :=
      (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child
    exact hs_children.2 hxs
  have hq2_sub_Q : branchSupport q.1.2 ⊆ Q := by
    intro x hx
    rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
    have hs_child : s ∈ TQ.Childs := hq_childs.2 hs
    have hs_children : s ∈ G.children n Q :=
      (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child
    exact hs_children.2 hxs
  have hAC : Disjoint (branchSupport q.1.1) (branchSupport p.1.1) :=
    (hQP_disj.mono_left hq1_sub_Q).mono_right hp1_sub_P
  have hAD : Disjoint (branchSupport q.1.1) (branchSupport p.1.2) :=
    (hQP_disj.mono_left hq1_sub_Q).mono_right hp2_sub_P
  have hBC : Disjoint (branchSupport q.1.2) (branchSupport p.1.1) :=
    (hQP_disj.mono_left hq2_sub_Q).mono_right hp1_sub_P
  have hBD : Disjoint (branchSupport q.1.2) (branchSupport p.1.2) :=
    (hQP_disj.mono_left hq2_sub_Q).mono_right hp2_sub_P
  rw [H.haarWavelets_def, H.haarWavelets_def]
  exact integral_mul_haarWavelet_eq_zero_of_disjoint
    G.μ (branchSupport q.1.1) (branchSupport q.1.2)
    (branchSupport p.1.1) (branchSupport p.1.2)
    hAC hAD hBC hBD



/-- Haar wavelets attached to different levels are orthogonal.  The deeper wavelet is either
inside one side of the coarser split, where the coarser wavelet is constant and the deeper
wavelet has mean zero, or it is disjoint from the coarser support. -/
theorem HaarSystem.integral_mul_haarWavelets_eq_zero_of_lt_level
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (n m : ℕ)
    (hnm : n < m)
    (Q : Set α)
    (hQ : Q ∈ G.grid.partitions n)
    (q : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree n Q hQ).Branches})
    (P : Set α)
    (hP : P ∈ G.grid.partitions m)
    (p : {r : Finset (Set α) × Finset (Set α) //
      r ∈ (H.binaryRefinement.tree m P hP).Branches}) :
    ∫ x, H.haarWavelets m P hP p x * H.haarWavelets n Q hQ q x ∂ G.μ = 0 := by
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  let TP := H.binaryRefinement.tree m P hP
  let TQ := H.binaryRefinement.tree n Q hQ
  have hp_childs : p.1.1 ⊆ TP.Childs ∧ p.1.2 ⊆ TP.Childs :=
    TP.TreeStructureChilds p.1 p.2
  have hq_childs : q.1.1 ⊆ TQ.Childs ∧ q.1.2 ⊆ TQ.Childs :=
    TQ.TreeStructureChilds q.1 q.2
  have hp1_part : ∀ s, s ∈ p.1.1 → s ∈ G.grid.partitions (m + 1) := by
    intro s hs
    have hs_child : s ∈ TP.Childs := hp_childs.1 hs
    exact (H.binaryRefinement.childs_are_children m P hP s).1 hs_child |>.1
  have hp2_part : ∀ s, s ∈ p.1.2 → s ∈ G.grid.partitions (m + 1) := by
    intro s hs
    have hs_child : s ∈ TP.Childs := hp_childs.2 hs
    exact (H.binaryRefinement.childs_are_children m P hP s).1 hs_child |>.1
  have hq1_part : ∀ s, s ∈ q.1.1 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    have hs_child : s ∈ TQ.Childs := hq_childs.1 hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child |>.1
  have hq2_part : ∀ s, s ∈ q.1.2 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    have hs_child : s ∈ TQ.Childs := hq_childs.2 hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child |>.1
  have hp_nonempty : p.1.1.Nonempty ∧ p.1.2.Nonempty := TP.NonemptyPairs p.1 p.2
  have hAB_cells : Disjoint p.1.1 p.1.2 := TP.DisjointComponents p.1 p.2
  have hCD_cells : Disjoint q.1.1 q.1.2 := TQ.DisjointComponents q.1 q.2
  have hp1_pos_cells : ∀ s, s ∈ p.1.1 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (m + 1) s (hp1_part s hs)
  have hp2_pos_cells : ∀ s, s ∈ p.1.2 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (m + 1) s (hp2_part s hs)
  have hAB : Disjoint (branchSupport p.1.1) (branchSupport p.1.2) :=
    disjoint_branchSupport_of_finset_disjoint G m p.1.1 p.1.2 hp1_part hp2_part hAB_cells
  have hCD : Disjoint (branchSupport q.1.1) (branchSupport q.1.2) :=
    disjoint_branchSupport_of_finset_disjoint G n q.1.1 q.1.2 hq1_part hq2_part hCD_cells
  have hA_meas : MeasurableSet (branchSupport p.1.1) :=
    measurableSet_branchSupport_of_partition G m p.1.1 hp1_part
  have hB_meas : MeasurableSet (branchSupport p.1.2) :=
    measurableSet_branchSupport_of_partition G m p.1.2 hp2_part
  have hA_pos : 0 < G.μ (branchSupport p.1.1) :=
    measure_branchSupport_pos_of_nonempty G p.1.1 hp1_pos_cells hp_nonempty.1
  have hB_pos : 0 < G.μ (branchSupport p.1.2) :=
    measure_branchSupport_pos_of_nonempty G p.1.2 hp2_pos_cells hp_nonempty.2
  have hp1_sub_P : branchSupport p.1.1 ⊆ P := by
    intro x hx
    rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
    have hs_child : s ∈ TP.Childs := hp_childs.1 hs
    have hs_children : s ∈ G.children m P :=
      (H.binaryRefinement.childs_are_children m P hP s).1 hs_child
    exact hs_children.2 hxs
  have hp2_sub_P : branchSupport p.1.2 ⊆ P := by
    intro x hx
    rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
    have hs_child : s ∈ TP.Childs := hp_childs.2 hs
    have hs_children : s ∈ G.children m P :=
      (H.binaryRefinement.childs_are_children m P hP s).1 hs_child
    exact hs_children.2 hxs
  have hq1_sub_Q : branchSupport q.1.1 ⊆ Q := by
    intro x hx
    rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
    have hs_child : s ∈ TQ.Childs := hq_childs.1 hs
    have hs_children : s ∈ G.children n Q :=
      (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child
    exact hs_children.2 hxs
  have hq2_sub_Q : branchSupport q.1.2 ⊆ Q := by
    intro x hx
    rcases (by simpa [branchSupport] using hx) with ⟨s, hs, hxs⟩
    have hs_child : s ∈ TQ.Childs := hq_childs.2 hs
    have hs_children : s ∈ G.children n Q :=
      (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child
    exact hs_children.2 hxs
  have hPQ_cases : P ⊆ Q ∨ Disjoint P Q :=
    G.partition_subset_or_disjoint_of_le n m hnm.le Q hQ P hP
  rcases hPQ_cases with hPQ_sub | hPQ_disj
  · obtain ⟨c, hc_child, hPc⟩ := G.exists_child_containing_of_lt n m hnm Q hQ P hP hPQ_sub
    have hc_in_childs : c ∈ TQ.Childs :=
      (H.binaryRefinement.childs_are_children n Q hQ c).2 hc_child
    have hp1_sub_c : branchSupport p.1.1 ⊆ c := hp1_sub_P.trans hPc
    have hp2_sub_c : branchSupport p.1.2 ⊆ c := hp2_sub_P.trans hPc
    by_cases hc_q1 : c ∈ q.1.1
    · have hsub : branchSupport p.1.1 ∪ branchSupport p.1.2 ⊆ branchSupport q.1.1 := by
        refine Set.union_subset ?_ ?_
        · exact hp1_sub_c.trans (subset_branchSupport_of_mem hc_q1)
        · exact hp2_sub_c.trans (subset_branchSupport_of_mem hc_q1)
      rw [H.haarWavelets_def, H.haarWavelets_def]
      exact integral_mul_haarWavelet_eq_zero_of_subset_left
        G.μ
        (branchSupport p.1.1) (branchSupport p.1.2)
        (branchSupport q.1.1) (branchSupport q.1.2)
        hAB hCD hsub hA_meas hB_meas hA_pos hB_pos
    · by_cases hc_q2 : c ∈ q.1.2
      · have hsub : branchSupport p.1.1 ∪ branchSupport p.1.2 ⊆ branchSupport q.1.2 := by
          refine Set.union_subset ?_ ?_
          · exact hp1_sub_c.trans (subset_branchSupport_of_mem hc_q2)
          · exact hp2_sub_c.trans (subset_branchSupport_of_mem hc_q2)
        rw [H.haarWavelets_def, H.haarWavelets_def]
        exact integral_mul_haarWavelet_eq_zero_of_subset_right
          G.μ
          (branchSupport p.1.1) (branchSupport p.1.2)
          (branchSupport q.1.1) (branchSupport q.1.2)
          hAB hCD hsub
          (measurableSet_branchSupport_of_partition G n q.1.1 hq1_part)
          hA_meas hB_meas hA_pos hB_pos
      · have hc_not_support : c ∉ q.1.1 ∪ q.1.2 := by
          simp [hc_q1, hc_q2]
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
        have hAC : Disjoint (branchSupport p.1.1) (branchSupport q.1.1) :=
          hc_q1_disj.mono_left hp1_sub_c
        have hAD : Disjoint (branchSupport p.1.1) (branchSupport q.1.2) :=
          hc_q2_disj.mono_left hp1_sub_c
        have hBC : Disjoint (branchSupport p.1.2) (branchSupport q.1.1) :=
          hc_q1_disj.mono_left hp2_sub_c
        have hBD : Disjoint (branchSupport p.1.2) (branchSupport q.1.2) :=
          hc_q2_disj.mono_left hp2_sub_c
        rw [H.haarWavelets_def, H.haarWavelets_def]
        exact integral_mul_haarWavelet_eq_zero_of_disjoint
          G.μ (branchSupport p.1.1) (branchSupport p.1.2)
          (branchSupport q.1.1) (branchSupport q.1.2)
          hAC hAD hBC hBD
  · have hAC : Disjoint (branchSupport p.1.1) (branchSupport q.1.1) :=
      (hPQ_disj.mono_left hp1_sub_P).mono_right hq1_sub_Q
    have hAD : Disjoint (branchSupport p.1.1) (branchSupport q.1.2) :=
      (hPQ_disj.mono_left hp1_sub_P).mono_right hq2_sub_Q
    have hBC : Disjoint (branchSupport p.1.2) (branchSupport q.1.1) :=
      (hPQ_disj.mono_left hp2_sub_P).mono_right hq1_sub_Q
    have hBD : Disjoint (branchSupport p.1.2) (branchSupport q.1.2) :=
      (hPQ_disj.mono_left hp2_sub_P).mono_right hq2_sub_Q
    rw [H.haarWavelets_def, H.haarWavelets_def]
    exact integral_mul_haarWavelet_eq_zero_of_disjoint
      G.μ (branchSupport p.1.1) (branchSupport p.1.2)
      (branchSupport q.1.1) (branchSupport q.1.2)
      hAC hAD hBC hBD

/-- Any two distinct globally indexed Haar wavelets are orthogonal.  This dispatches to the
same-cell, same-level different-cell, and different-level orthogonality lemmas. -/
theorem HaarSystem.integral_mul_wavelet_eq_zero_of_ne
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i j : H.Index)
    (hij : i ≠ j) :
  ∫ x, HaarSystem.wavelet G H i x * HaarSystem.wavelet G H j x ∂ G.μ = 0 := by
  rcases i with ⟨ni, Qi, hQi, pi⟩
  rcases j with ⟨nj, Qj, hQj, pj⟩
  dsimp [HaarSystem.wavelet]
  rcases lt_trichotomy ni nj with hlt | hEq | hgt
  · have hswap :
        ∫ x, H.haarWavelets nj Qj hQj pj x * H.haarWavelets ni Qi hQi pi x ∂ G.μ = 0 :=
      HaarSystem.integral_mul_haarWavelets_eq_zero_of_lt_level
        G H ni nj hlt Qi hQi pi Qj hQj pj
    have hmul_comm :
        (fun x => H.haarWavelets ni Qi hQi pi x * H.haarWavelets nj Qj hQj pj x)
          = (fun x => H.haarWavelets nj Qj hQj pj x * H.haarWavelets ni Qi hQi pi x) := by
      funext x
      rw [mul_comm]
    rw [hmul_comm]
    exact hswap
  · subst hEq
    by_cases hQQ : Qi = Qj
    · subst hQQ
      have hproof : hQi = hQj := Subsingleton.elim _ _
      subst hQj
      have hpij : pi ≠ pj := by
        intro hpij
        apply hij
        cases hpij
        rfl
      exact HaarSystem.integral_mul_haarWavelets_eq_zero_of_distinct
        G H ni Qi hQi pi pj hpij
    · exact HaarSystem.integral_mul_haarWavelets_eq_zero_of_distinct_distinct_Q
        G H ni Qi hQi Qj hQj pi pj (by
          intro h
          apply hQQ
          exact h.symm)
  · exact HaarSystem.integral_mul_haarWavelets_eq_zero_of_lt_level
      G H nj ni hgt Qj hQj pj Qi hQi pi

/-- Every globally indexed Haar wavelet has zero mean. -/
theorem HaarSystem.integral_wavelet_eq_zero
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    ∫ x, HaarSystem.wavelet G H i x ∂ G.μ = 0 := by
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  rcases i with ⟨n, Q, hQ, p⟩
  dsimp [HaarSystem.wavelet]
  let T := H.binaryRefinement.tree n Q hQ
  have hp_childs : p.1.1 ⊆ T.Childs ∧ p.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds p.1 p.2
  have hp1_part : ∀ s, s ∈ p.1.1 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    have hs_child : s ∈ T.Childs := hp_childs.1 hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child |>.1
  have hp2_part : ∀ s, s ∈ p.1.2 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    have hs_child : s ∈ T.Childs := hp_childs.2 hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 hs_child |>.1
  have hp_nonempty : p.1.1.Nonempty ∧ p.1.2.Nonempty := T.NonemptyPairs p.1 p.2
  have hAB_cells : Disjoint p.1.1 p.1.2 := T.DisjointComponents p.1 p.2
  have hp1_pos_cells : ∀ s, s ∈ p.1.1 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (n + 1) s (hp1_part s hs)
  have hp2_pos_cells : ∀ s, s ∈ p.1.2 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (n + 1) s (hp2_part s hs)
  have hAB : Disjoint (branchSupport p.1.1) (branchSupport p.1.2) :=
    disjoint_branchSupport_of_finset_disjoint G n p.1.1 p.1.2 hp1_part hp2_part hAB_cells
  have hA_meas : MeasurableSet (branchSupport p.1.1) :=
    measurableSet_branchSupport_of_partition G n p.1.1 hp1_part
  have hB_meas : MeasurableSet (branchSupport p.1.2) :=
    measurableSet_branchSupport_of_partition G n p.1.2 hp2_part
  have hA_pos : 0 < G.μ (branchSupport p.1.1) :=
    measure_branchSupport_pos_of_nonempty G p.1.1 hp1_pos_cells hp_nonempty.1
  have hB_pos : 0 < G.μ (branchSupport p.1.2) :=
    measure_branchSupport_pos_of_nonempty G p.1.2 hp2_pos_cells hp_nonempty.2
  rw [H.haarWavelets_def]
  exact integral_haarWavelet_eq_zero_of_pos
    G.μ (branchSupport p.1.1) (branchSupport p.1.2)
    hAB hA_meas hB_meas hA_pos hB_pos

/-- Every globally indexed Haar wavelet is integrable. -/
theorem HaarSystem.integrable_wavelet
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    MeasureTheory.Integrable (H.wavelet G i) G.μ := by
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  rcases i with ⟨n, Q, hQ, p⟩
  dsimp [HaarSystem.wavelet]
  let T := H.binaryRefinement.tree n Q hQ
  have hp_childs : p.1.1 ⊆ T.Childs ∧ p.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds p.1 p.2
  have hp1_part : ∀ s, s ∈ p.1.1 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hp_childs.1 hs) |>.1
  have hp2_part : ∀ s, s ∈ p.1.2 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hp_childs.2 hs) |>.1
  have hA_meas : MeasurableSet (branchSupport p.1.1) :=
    measurableSet_branchSupport_of_partition G n p.1.1 hp1_part
  have hB_meas : MeasurableSet (branchSupport p.1.2) :=
    measurableSet_branchSupport_of_partition G n p.1.2 hp2_part
  rw [H.haarWavelets_def]
  exact integrable_haarWavelet G.μ (branchSupport p.1.1) (branchSupport p.1.2)
    hA_meas hB_meas

/-- The product of two globally indexed Haar wavelets is integrable. -/
theorem HaarSystem.integrable_wavelet_mul_wavelet
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i j : H.Index) :
    MeasureTheory.Integrable (fun x => H.wavelet G i x * H.wavelet G j x) G.μ := by
  rcases j with ⟨n, Q, hQ, p⟩
  exact (H.integrable_wavelet G i).mul_bdd
    (c := ‖(1 / (G.μ (branchSupport p.1.1)).toReal : ℝ)‖ +
      ‖(1 / (G.μ (branchSupport p.1.2)).toReal : ℝ)‖)
    (H.integrable_wavelet G { level := n, cell := Q, hcell := hQ, branch := p }).aestronglyMeasurable
    (by
      dsimp [HaarSystem.wavelet]
      exact Filter.Eventually.of_forall
        (by
          intro x
          simpa [H.haarWavelets_def] using
            norm_haarWavelet_le G.μ (branchSupport p.1.1) (branchSupport p.1.2) x))

/-- The square integral of a globally indexed Haar wavelet is positive. -/
theorem HaarSystem.integral_wavelet_mul_self_pos
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    0 < ∫ x, H.wavelet G i x * H.wavelet G i x ∂G.μ := by
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  rcases i with ⟨n, Q, hQ, p⟩
  dsimp [HaarSystem.wavelet]
  let T := H.binaryRefinement.tree n Q hQ
  have hp_childs : p.1.1 ⊆ T.Childs ∧ p.1.2 ⊆ T.Childs :=
    T.TreeStructureChilds p.1 p.2
  have hp1_part : ∀ s, s ∈ p.1.1 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hp_childs.1 hs) |>.1
  have hp2_part : ∀ s, s ∈ p.1.2 → s ∈ G.grid.partitions (n + 1) := by
    intro s hs
    exact (H.binaryRefinement.childs_are_children n Q hQ s).1 (hp_childs.2 hs) |>.1
  have hp_nonempty : p.1.1.Nonempty ∧ p.1.2.Nonempty := T.NonemptyPairs p.1 p.2
  have hAB_cells : Disjoint p.1.1 p.1.2 := T.DisjointComponents p.1 p.2
  have hp1_pos_cells : ∀ s, s ∈ p.1.1 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (n + 1) s (hp1_part s hs)
  have hp2_pos_cells : ∀ s, s ∈ p.1.2 → 0 < G.μ s := by
    intro s hs
    exact G.positive_measure (n + 1) s (hp2_part s hs)
  have hAB : Disjoint (branchSupport p.1.1) (branchSupport p.1.2) :=
    disjoint_branchSupport_of_finset_disjoint G n p.1.1 p.1.2 hp1_part hp2_part hAB_cells
  have hA_meas : MeasurableSet (branchSupport p.1.1) :=
    measurableSet_branchSupport_of_partition G n p.1.1 hp1_part
  have hB_meas : MeasurableSet (branchSupport p.1.2) :=
    measurableSet_branchSupport_of_partition G n p.1.2 hp2_part
  have hA_pos : 0 < G.μ (branchSupport p.1.1) :=
    measure_branchSupport_pos_of_nonempty G p.1.1 hp1_pos_cells hp_nonempty.1
  have hB_pos : 0 < G.μ (branchSupport p.1.2) :=
    measure_branchSupport_pos_of_nonempty G p.1.2 hp2_pos_cells hp_nonempty.2
  have hA_toReal_pos : 0 < (G.μ (branchSupport p.1.1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hA_pos)
      (MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport p.1.1)).ne
  have hB_toReal_pos : 0 < (G.μ (branchSupport p.1.2)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hB_pos)
      (MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport p.1.2)).ne
  rw [H.haarWavelets_def,
    integral_haarWavelet_mul_self_eq G.μ (branchSupport p.1.1) (branchSupport p.1.2)
      hAB hA_meas hB_meas hA_pos hB_pos]
  positivity

/-- The square integral of a globally indexed Haar wavelet is nonzero. -/
theorem HaarSystem.integral_wavelet_mul_self_ne_zero
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G))
    (i : H.Index) :
    (∫ x, H.wavelet G i x * H.wavelet G i x ∂G.μ) ≠ 0 :=
  ne_of_gt (H.integral_wavelet_mul_self_pos G i)



/-- Distinct functions in the full Haar system are orthogonal: father versus wavelet uses the
zero mean of wavelets, and wavelet versus wavelet uses global Haar-wavelet orthogonality. -/
theorem FullHaarSystem.integral_mul_function_eq_zero_of_ne
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (i j : F.Index)
    (hij : i ≠ j) :
    ∫ x, FullHaarSystem.function G F i x * FullHaarSystem.function G F j x ∂ G.μ = 0 := by
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  cases i with
  | alpha =>
      cases j with
      | alpha =>
          exact (hij rfl).elim
      | wavelet jw =>
          rw [FullHaarSystem.function, FullHaarSystem.function, F.alphaFunction_def]
          let c : ℝ := 1 / (G.μ Set.univ).toReal
          have hmul_eq :
              (fun x => normalizedAlphaFunction G x * HaarSystem.wavelet G F.toHaarSystem jw x)
                = (fun x => c * HaarSystem.wavelet G F.toHaarSystem jw x) := by
            funext x
            simp [normalizedAlphaFunction, c]
          rw [hmul_eq, MeasureTheory.integral_const_mul]
          rw [HaarSystem.integral_wavelet_eq_zero G F.toHaarSystem jw]
          simp
  | wavelet iw =>
      cases j with
      | alpha =>
          rw [FullHaarSystem.function, FullHaarSystem.function, F.alphaFunction_def]
          let c : ℝ := 1 / (G.μ Set.univ).toReal
          have hmul_eq :
              (fun x => HaarSystem.wavelet G F.toHaarSystem iw x * normalizedAlphaFunction G x)
                = (fun x => c * HaarSystem.wavelet G F.toHaarSystem iw x) := by
            funext x
            simp [normalizedAlphaFunction, c, mul_comm]
          rw [hmul_eq, MeasureTheory.integral_const_mul]
          rw [HaarSystem.integral_wavelet_eq_zero G F.toHaarSystem iw]
          simp
      | wavelet jw =>
          have hiw_jw : iw ≠ jw := by
            intro h
            apply hij
            cases h
            rfl
          simpa [FullHaarSystem.function]
            using HaarSystem.integral_mul_wavelet_eq_zero_of_ne G F.toHaarSystem iw jw hiw_jw

end UnbalancedHaarWavelet
