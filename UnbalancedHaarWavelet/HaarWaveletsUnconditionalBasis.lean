import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Denumerable
import UnbalancedHaarWavelet.GridDefinition
import UnbalancedHaarWavelet.HaarWavelets_def_Martingale
import UnbalancedHaarWavelet.HaarWaveletsDenseSpan
import UnconditionalSchauderBasis.UnconditionalSchauderBasisNontrivialField

/-!
This file proves the unconditional-basis result for the full Haar family in
`Lp`, in the range `1 < p < ∞`, over a finite-measure grid setting.

Big picture: first we get a finite-sign estimate from Burkholder-type bounds,
then we combine that with density of the Haar span to build an unconditional
Schauder basis.
-/
set_option linter.style.header false

namespace UnbalancedHaarWavelet

open UnconditionalCriterion

/--
Core finite-sum estimate for the full Haar family.

Idea: split off the `alpha` term, rewrite the rest as a wavelet-only sum, then
apply the known Burkholder estimate for finite wavelet combinations.
-/
theorem FullHaarSystem.eLpNorm_finite_sum_le_Burkholder
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (p : ENNReal) (hp_one : 1 < p) (hfin : p ≠ ⊤)
    (t : Finset F.Index) (a c : F.Index → ℝ)
    (hc : ∀ i, i ∈ t → |c i| ≤ 1) :
    MeasureTheory.eLpNorm (fun x => ∑ i ∈ t, c i * a i * F.function G i x) p G.μ ≤
      ENNReal.ofReal (Burkholder.pStar p.toReal - 1) *
        MeasureTheory.eLpNorm (fun x => ∑ i ∈ t, a i * F.function G i x) p G.μ := by
  classical
  let H : HaarSystem (G := G) := F.toHaarSystem
  let alphaIndex : F.Index := .alpha
  let alphaValue : ℝ := 1 / (G.μ Set.univ).toReal
  let sw : Finset H.Index :=
    t.filterMap
      (fun i => match i with
        | .alpha => none
        | .wavelet j => some j)
      (by
        intro i1 i2 b h1 h2
        cases i1 <;> cases i2 <;> cases h1 <;> cases h2
        rfl)
  let a0 : ℝ := if h : alphaIndex ∈ t then a alphaIndex * alphaValue else 0
  let c0 : ℝ := if h : alphaIndex ∈ t then c alphaIndex else 0
  let aw : H.Index → ℝ := fun j => a (.wavelet j)
  let cw : H.Index → ℝ := fun j => c (.wavelet j)
  have hcw : ∀ j, j ∈ sw → |cw j| ≤ 1 := by
    intro j hj
    rw [Finset.mem_filterMap] at hj
    rcases hj with ⟨i, hi, hsome⟩
    cases i with
    | alpha => cases hsome
    | wavelet k =>
        cases hsome
        simpa [cw] using hc (.wavelet j) hi
  have hc0 : |c0| ≤ 1 := by
    by_cases hα : alphaIndex ∈ t
    · simpa [c0, hα, alphaIndex] using hc alphaIndex hα
    · simp [c0, hα]
  have hsum_wavelets_signed :
      ∀ x,
        ∑ i ∈ t.erase alphaIndex, c i * a i * F.function G i x =
          ∑ j ∈ sw, cw j * aw j * H.wavelet G j x := by
    intro x
    refine Finset.sum_bij'
      (i := fun i hi => match i with
        | .alpha => by
            exfalso
            exact (Finset.mem_erase.mp hi).1 rfl
        | .wavelet j => j)
      (j := fun j _hj => FullHaarSystem.Index.wavelet j)
      ?_ ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filterMap]
      refine ⟨i, (Finset.mem_of_mem_erase hi), ?_⟩
      cases i with
      | alpha =>
          exfalso
          exact (Finset.mem_erase.mp hi).1 rfl
      | wavelet j => rfl
    · intro j hj
      refine Finset.mem_erase.mpr ?_
      constructor
      · simp [alphaIndex]
      · rw [Finset.mem_filterMap] at hj
        rcases hj with ⟨i, hi, hsome⟩
        cases i with
        | alpha => cases hsome
        | wavelet k =>
            cases hsome
            simpa using hi
    · intro i hi
      cases i with
      | alpha =>
          exfalso
          exact (Finset.mem_erase.mp hi).1 rfl
      | wavelet k => rfl
    · intro j hj
      rfl
    · intro i hi
      cases i with
      | alpha =>
          exfalso
          exact (Finset.mem_erase.mp hi).1 rfl
      | wavelet j =>
          simp [cw, aw, H, FullHaarSystem.function, HaarSystem.wavelet,
          mul_assoc, mul_comm]
  have hsum_wavelets_plain :
      ∀ x,
        ∑ i ∈ t.erase alphaIndex, a i * F.function G i x =
          ∑ j ∈ sw, aw j * H.wavelet G j x := by
    intro x
    refine Finset.sum_bij'
      (i := fun i hi => match i with
        | .alpha => by
            exfalso
            exact (Finset.mem_erase.mp hi).1 rfl
        | .wavelet j => j)
      (j := fun j _hj => FullHaarSystem.Index.wavelet j)
      ?_ ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filterMap]
      refine ⟨i, (Finset.mem_of_mem_erase hi), ?_⟩
      cases i with
      | alpha =>
          exfalso
          exact (Finset.mem_erase.mp hi).1 rfl
      | wavelet j => rfl
    · intro j hj
      refine Finset.mem_erase.mpr ?_
      constructor
      · simp [alphaIndex]
      · rw [Finset.mem_filterMap] at hj
        rcases hj with ⟨i, hi, hsome⟩
        cases i with
        | alpha => cases hsome
        | wavelet k =>
            cases hsome
            simpa using hi
    · intro i hi
      cases i with
      | alpha =>
          exfalso
          exact (Finset.mem_erase.mp hi).1 rfl
      | wavelet k => rfl
    · intro j hj
      rfl
    · intro i hi
      cases i with
      | alpha =>
          exfalso
          exact (Finset.mem_erase.mp hi).1 rfl
      | wavelet j =>
          simp [aw, H, FullHaarSystem.function, HaarSystem.wavelet]
  have hsigned :
      (fun x => ∑ i ∈ t, c i * a i * F.function G i x)
        =
      (fun x => a0 * c0 + ∑ j ∈ sw, cw j * aw j * H.wavelet G j x) := by
    funext x
    by_cases hα : alphaIndex ∈ t
    · rw [← Finset.insert_erase hα, Finset.sum_insert (Finset.notMem_erase _ _)]
      have halpha : F.function G alphaIndex x = alphaValue := by
        simp [FullHaarSystem.function, F.alphaFunction_def, normalizedAlphaFunction, alphaIndex,
          alphaValue]
      rw [halpha, hsum_wavelets_signed x]
      simp [a0, c0, hα, alphaValue, mul_assoc, mul_left_comm, mul_comm]
    · have ht : t.erase alphaIndex = t := Finset.erase_eq_of_notMem hα
      simpa [a0, c0, hα, ht] using hsum_wavelets_signed x
  have hplain :
      (fun x => ∑ i ∈ t, a i * F.function G i x)
        =
      (fun x => a0 + ∑ j ∈ sw, aw j * H.wavelet G j x) := by
    funext x
    by_cases hα : alphaIndex ∈ t
    · rw [← Finset.insert_erase hα, Finset.sum_insert (Finset.notMem_erase _ _)]
      have halpha : F.function G alphaIndex x = alphaValue := by
        simp [FullHaarSystem.function, F.alphaFunction_def, normalizedAlphaFunction, alphaIndex,
          alphaValue]
      rw [halpha, hsum_wavelets_plain x]
      simp [a0, hα, alphaValue, mul_comm]
    · have ht : t.erase alphaIndex = t := Finset.erase_eq_of_notMem hα
      simpa [a0, hα, ht] using hsum_wavelets_plain x
  calc
    MeasureTheory.eLpNorm (fun x => ∑ i ∈ t, c i * a i * F.function G i x) p G.μ
        = MeasureTheory.eLpNorm (fun x => a0 * c0 + ∑ j ∈ sw, cw j * aw j * H.wavelet G j x) p G.μ := by
            rw [hsigned]
    _ ≤ ENNReal.ofReal (Burkholder.pStar p.toReal - 1) *
          MeasureTheory.eLpNorm (fun x => a0 + ∑ j ∈ sw, aw j * H.wavelet G j x) p G.μ := by
          exact HaarSystem.eLpNorm_finite_wavelet_sum_le_Burkholder_2
            G H p hp_one hfin sw aw cw a0 c0 hcw hc0
    _ = ENNReal.ofReal (Burkholder.pStar p.toReal - 1) *
          MeasureTheory.eLpNorm (fun x => ∑ i ∈ t, a i * F.function G i x) p G.μ := by
          rw [hplain]

/--
Moves the finite Burkholder estimate to an arbitrary enumeration of the full
Haar family in `Lp`.

In plain terms: if each coefficient `ε n` is in `{-1, 1}`, then the signed
finite sum is controlled by the same constant times the unsigned one.
-/
theorem FullHaarSystem.hasFiniteSignBound_of_memLp
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (p : ENNReal) [Fact (1 ≤ p)]
    (hp_one : 1 < p) (hfin : p ≠ ⊤)
    (hC : 0 ≤ Burkholder.pStar p.toReal - 1)
    (e : ℕ ≃ F.Index)
  (hmem : ∀ i : F.Index, MeasureTheory.MemLp (F.function G i) p G.μ) :
    HasFiniteSignBound (𝕜 := ℝ)
      (fun n => (hmem (e n)).toLp (F.function G (e n)))
      (Burkholder.pStar p.toReal - 1) := by
  classical
  intro s a ε hε
  let t : Finset F.Index := s.image e
  let aF : F.Index → ℝ := fun i => a (e.symm i)
  let εF : F.Index → ℝ := fun i => ε (e.symm i)
  -- These are the concrete finite sums in function form.
  let plainFun : α → ℝ := fun x => ∑ n ∈ s, a n * F.function G (e n) x
  let signFun : α → ℝ := fun x => ∑ n ∈ s, (ε n * a n) * F.function G (e n) x
  let xEnum : ℕ → FullHaarLpSpace G p := fun n => (hmem (e n)).toLp (F.function G (e n))
  have hεF : ∀ i, i ∈ t → |εF i| ≤ 1 := by
    intro i hi
    have hi' : i ∈ s.image e := by simpa [t] using hi
    rw [Finset.mem_image] at hi'
    rcases hi' with ⟨n, hn, rfl⟩
    rcases hε n hn with h | h <;> simp [εF, h]
  have hsum_plain :
      (fun x => ∑ i ∈ t, aF i * F.function G i x) = plainFun := by
    funext x
    refine Finset.sum_bijective e.symm e.symm.bijective ?_ ?_
    · intro n
      constructor
      · intro hn
        rcases Finset.mem_image.mp (by simpa [t] using hn) with ⟨m, hm, hmn⟩
        have hm' : m = e.symm n := by simpa using congrArg e.symm hmn
        simpa [hm'] using hm
      · intro hn
        have hn' : e (e.symm n) ∈ s.image e := Finset.mem_image.mpr ⟨e.symm n, hn, by simp⟩
        simpa [t] using hn'
    · intro n hn
      simp [aF]
  have hsum_signed :
      (fun x => ∑ i ∈ t, εF i * aF i * F.function G i x) = signFun := by
    funext x
    refine Finset.sum_bijective e.symm e.symm.bijective ?_ ?_
    · intro n
      constructor
      · intro hn
        rcases Finset.mem_image.mp (by simpa [t] using hn) with ⟨m, hm, hmn⟩
        have hm' : m = e.symm n := by simpa using congrArg e.symm hmn
        simpa [hm'] using hm
      · intro hn
        have hn' : e (e.symm n) ∈ s.image e := Finset.mem_image.mpr ⟨e.symm n, hn, by simp⟩
        simpa [t] using hn'
    · intro n hn
      simp [aF, εF, mul_comm]
  -- Convert function inequalities to norm inequalities in `Lp`.
  have hplain_mem : MeasureTheory.MemLp plainFun p G.μ := by
    dsimp [plainFun]
    exact MeasureTheory.memLp_finsetSum s (fun n _ => (hmem (e n)).const_smul (a n))
  have hsign_mem : MeasureTheory.MemLp signFun p G.μ := by
    dsimp [signFun]
    exact MeasureTheory.memLp_finsetSum s (fun n _ => (hmem (e n)).const_smul (ε n * a n))
  have hnorm_plain :
      ‖∑ n ∈ s, a n • xEnum n‖ = ENNReal.toReal (MeasureTheory.eLpNorm plainFun p G.μ) := by
    rw [toLp_finsetSum_const_smul p s (fun n => F.function G (e n)) (fun n => hmem (e n)) a]
    exact MeasureTheory.Lp.norm_toLp _ hplain_mem
  have hnorm_signed :
      ‖∑ n ∈ s, (ε n * a n) • xEnum n‖ = ENNReal.toReal (MeasureTheory.eLpNorm signFun p G.μ) := by
    rw [toLp_finsetSum_const_smul p s (fun n => F.function G (e n)) (fun n => hmem (e n))
      (fun n => ε n * a n)]
    exact MeasureTheory.Lp.norm_toLp _ hsign_mem
  have heLp :
      MeasureTheory.eLpNorm signFun p G.μ ≤
        ENNReal.ofReal (Burkholder.pStar p.toReal - 1) * MeasureTheory.eLpNorm plainFun p G.μ := by
    have hcore := FullHaarSystem.eLpNorm_finite_sum_le_Burkholder G F p hp_one hfin t aF εF hεF
    rw [hsum_signed, hsum_plain] at hcore
    exact hcore
  have hreal :
      ENNReal.toReal (MeasureTheory.eLpNorm signFun p G.μ)
        ≤ (Burkholder.pStar p.toReal - 1) * ENNReal.toReal (MeasureTheory.eLpNorm plainFun p G.μ) := by
    have htop :
        ENNReal.ofReal (Burkholder.pStar p.toReal - 1) * MeasureTheory.eLpNorm plainFun p G.μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hplain_mem.eLpNorm_ne_top
    exact by
      simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono htop heLp
  calc
    ‖∑ n ∈ s, (ε n * a n) • xEnum n‖
        = ENNReal.toReal (MeasureTheory.eLpNorm signFun p G.μ) := hnorm_signed
    _ ≤ (Burkholder.pStar p.toReal - 1) * ENNReal.toReal (MeasureTheory.eLpNorm plainFun p G.μ) :=
      hreal
    _ = (Burkholder.pStar p.toReal - 1) * ‖∑ n ∈ s, a n • xEnum n‖ := by
      rw [hnorm_plain]

/--
Shows each full Haar function is in `Lp`.

`alpha` is a normalized constant function, and a wavelet is a difference of two
indicator pieces, so both cases are handled directly.
-/
theorem FullHaarSystem.memLp_function
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (p : ENNReal) [Fact (1 ≤ p)]
    (i : F.Index) :
    MeasureTheory.MemLp (F.function G i) p G.μ := by
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  cases i with
  | alpha =>
      rw [FullHaarSystem.function, F.alphaFunction_def]
      change MeasureTheory.MemLp
        (Set.indicator (Set.univ : Set α) (fun _ => 1 / (G.μ Set.univ).toReal)) p G.μ
      exact MeasureTheory.memLp_indicator_const p MeasurableSet.univ
        (1 / (G.μ Set.univ).toReal)
        (Or.inr (MeasureTheory.measure_lt_top G.μ Set.univ).ne)
  | wavelet j =>
      let T := F.binaryRefinement.tree j.level j.cell j.hcell
      have hp_childs : j.branch.1.1 ⊆ T.Childs ∧ j.branch.1.2 ⊆ T.Childs :=
        T.TreeStructureChilds j.branch.1 j.branch.2
      have hp1_part : ∀ s, s ∈ j.branch.1.1 → s ∈ G.grid.partitions (j.level + 1) := by
        intro s hs
        exact (F.binaryRefinement.childs_are_children j.level j.cell j.hcell s).1
          (hp_childs.1 hs) |>.1
      have hp2_part : ∀ s, s ∈ j.branch.1.2 → s ∈ G.grid.partitions (j.level + 1) := by
        intro s hs
        exact (F.binaryRefinement.childs_are_children j.level j.cell j.hcell s).1
          (hp_childs.2 hs) |>.1
      have hA_meas : MeasurableSet (branchSupport j.branch.1.1) :=
        measurableSet_branchSupport_of_partition G j.level j.branch.1.1 hp1_part
      have hB_meas : MeasurableSet (branchSupport j.branch.1.2) :=
        measurableSet_branchSupport_of_partition G j.level j.branch.1.2 hp2_part
      have hA_mem :
          MeasureTheory.MemLp
            (Set.indicator (branchSupport j.branch.1.1)
              (fun _ => 1 / (G.μ (branchSupport j.branch.1.1)).toReal)) p G.μ := by
        simpa using MeasureTheory.memLp_indicator_const p hA_meas
          (1 / (G.μ (branchSupport j.branch.1.1)).toReal)
          (Or.inr (MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport j.branch.1.1)).ne)
      have hB_mem :
          MeasureTheory.MemLp
            (Set.indicator (branchSupport j.branch.1.2)
              (fun _ => 1 / (G.μ (branchSupport j.branch.1.2)).toReal)) p G.μ := by
        simpa using MeasureTheory.memLp_indicator_const p hB_meas
          (1 / (G.μ (branchSupport j.branch.1.2)).toReal)
          (Or.inr (MeasureTheory.measure_lt_top (μ := G.μ) (branchSupport j.branch.1.2)).ne)
      rw [FullHaarSystem.function, HaarSystem.wavelet, F.haarWavelets_def]
      change MeasureTheory.MemLp
        ((Set.indicator (branchSupport j.branch.1.1)
            (fun _ => 1 / (G.μ (branchSupport j.branch.1.1)).toReal))
          - (Set.indicator (branchSupport j.branch.1.2)
            (fun _ => 1 / (G.μ (branchSupport j.branch.1.2)).toReal))) p G.μ
      exact hA_mem.sub hB_mem

/--
The `Lp` class of a full Haar function is never zero.

Proof sketch: if the class were zero, the function would be almost everywhere
zero, so its self-product integral would vanish; that contradicts known
non-vanishing of the corresponding Haar energy.
-/
theorem FullHaarSystem.toLp_function_ne_zero
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (p : ENNReal) [Fact (1 ≤ p)]
    (hmem : ∀ i : F.Index, MeasureTheory.MemLp (F.function G i) p G.μ)
    (i : F.Index) :
    (hmem i).toLp (F.function G i) ≠ 0 := by
  intro hzero
  have h_ae_zero : F.function G i =ᵐ[G.μ] 0 := by
    refine (MeasureTheory.MemLp.coeFn_toLp (hmem i)).symm.trans ?_
    simpa [hzero] using (MeasureTheory.Lp.coeFn_zero (E := ℝ) (p := p) (μ := G.μ))
  have hsq_ae_zero :
      (fun x => F.function G i x * F.function G i x) =ᵐ[G.μ] 0 := by
    filter_upwards [h_ae_zero] with x hx
    simp [hx]
  have hintegral_zero :
      ∫ x, F.function G i x * F.function G i x ∂G.μ = 0 := by
    simpa using MeasureTheory.integral_congr_ae hsq_ae_zero
  cases i with
  | alpha =>
      letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
      let c : ℝ := 1 / (G.μ Set.univ).toReal
      have hμuniv_pos : 0 < G.μ Set.univ := by
        simpa [G.grid.first_partition_eq_univ] using
          G.positive_measure 0 Set.univ (by simp [G.grid.first_partition_eq_univ])
      have hc_ne : c ≠ 0 := by
        apply one_div_ne_zero
        exact ENNReal.toReal_ne_zero.mpr
          ⟨ne_of_gt hμuniv_pos, (MeasureTheory.measure_lt_top G.μ Set.univ).ne⟩
      have hμreal_ne : G.μ.real Set.univ ≠ 0 := by
        exact (ENNReal.toReal_pos hμuniv_pos.ne' (MeasureTheory.measure_lt_top G.μ Set.univ).ne).ne'
      have hself_ne :
          ∫ x, F.function G FullHaarSystem.Index.alpha x *
              F.function G FullHaarSystem.Index.alpha x ∂G.μ ≠ 0 := by
        rw [FullHaarSystem.function, F.alphaFunction_def]
        have hconst :
            (fun x => normalizedAlphaFunction G x * normalizedAlphaFunction G x)
              = fun _ => c * c := by
          funext x
          simp [normalizedAlphaFunction, c]
        rw [hconst, MeasureTheory.integral_const]
        simp [smul_eq_mul, hμreal_ne, hc_ne]
      exact hself_ne hintegral_zero
  | wavelet j =>
      have hself_ne :
          ∫ x, F.function G (.wavelet j) x * F.function G (.wavelet j) x ∂G.μ ≠ 0 := by
        simpa [FullHaarSystem.function] using
          HaarSystem.integral_wavelet_mul_self_ne_zero G F.toHaarSystem j
      exact hself_ne hintegral_zero

/--
Packages a Haar index as explicit level/cell/branch data.

This is just a bookkeeping equivalence used later for countability.
-/
noncomputable def HaarSystem.Index.equivSigma
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    H.Index ≃
      Σ n : ℕ,
        Σ cell : {Q : Set α // Q ∈ G.grid.partitions n},
          {r : Finset (Set α) × Finset (Set α) //
            r ∈ (H.binaryRefinement.tree n cell.1 cell.2).Branches} where
  toFun i := ⟨i.level, ⟨⟨i.cell, i.hcell⟩, i.branch⟩⟩
  invFun x :=
    { level := x.1
      cell := x.2.1.1
      hcell := x.2.1.2
      branch := x.2.2 }
  left_inv i := by
    cases i
    rfl
  right_inv x := by
    cases x with
    | mk n x =>
        cases x with
        | mk cell branch =>
            cases cell
            rfl

/--
Countability of Haar indices, obtained from the sigma representation above.
-/
theorem HaarSystem.Index.countable
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    Countable H.Index := by
  classical
  let e := HaarSystem.Index.equivSigma G H
  exact e.injective.countable

/--
Chooses a canonical Haar index at each level by taking a root branch of some
cell in that level partition.
-/
noncomputable def HaarSystem.Index.rootAtLevel
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) (n : ℕ) : H.Index := by
  classical
  have huniv_nonempty : (Set.univ : Set α).Nonempty := by
    simpa using G.partition_nonempty 0 Set.univ (by simp [G.grid.first_partition_eq_univ])
  have hpart_nonempty : (G.grid.partitions n).Nonempty := by
    by_contra h_empty
    have hempty : G.grid.partitions n = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_empty
    have huniv_eq_empty : (Set.univ : Set α) = ∅ := by
      simpa [hempty] using (G.grid.covering n).symm
    simp [huniv_eq_empty] at huniv_nonempty
  let Q : Set α := Classical.choose (show ∃ Q, Q ∈ G.grid.partitions n from hpart_nonempty)
  have hQ : Q ∈ G.grid.partitions n :=
    Classical.choose_spec (show ∃ Q, Q ∈ G.grid.partitions n from hpart_nonempty)
  let T := H.binaryRefinement.tree n Q hQ
  exact
    { level := n
      cell := Q
      hcell := hQ
      branch := ⟨T.Root, T.RootinBranches⟩ }

    /--
    Infinitude of Haar indices, witnessed by sending each natural number to the
    chosen root index at that level.
    -/
theorem HaarSystem.Index.infinite
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (H : HaarSystem (G := G)) :
    Infinite H.Index := by
  classical
  refine Infinite.of_injective (fun n => HaarSystem.Index.rootAtLevel G H n) ?_
  intro n m hnm
  exact congrArg HaarSystem.Index.level hnm

/--
Splits full Haar indices into either the special `alpha` index or a wavelet
index.
-/
noncomputable def FullHaarSystem.Index.equivOption
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G)) :
    F.Index ≃ Option F.toHaarSystem.Index where
  toFun i :=
    match i with
    | .alpha => none
    | .wavelet j => some j
  invFun i :=
    match i with
    | none => .alpha
    | some j => .wavelet j
  left_inv i := by
    cases i <;> rfl
  right_inv i := by
    cases i <;> rfl

/--
Builds an enumeration of full Haar indices by combining countability and
infinitude.
-/
theorem FullHaarSystem.index_nonempty_equiv_nat
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G)) :
    Nonempty (ℕ ≃ F.Index) := by
  classical
  let H : HaarSystem (G := G) := F.toHaarSystem
  letI : Countable H.Index := HaarSystem.Index.countable G H
  letI : Infinite H.Index := HaarSystem.Index.infinite G H
  letI : Countable F.Index :=
    (FullHaarSystem.Index.equivOption G F).injective.countable
  letI : Infinite F.Index :=
    Infinite.of_injective
      (FullHaarSystem.Index.equivOption G F).symm
      (FullHaarSystem.Index.equivOption G F).symm.injective
  simpa using (nonempty_equiv_of_countable (α := ℕ) (β := F.Index))

/--
Concrete chosen enumeration of full Haar indices.
-/
noncomputable def FullHaarSystem.indexEquivNat
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G)) :
    ℕ ≃ F.Index :=
  Classical.choice (FullHaarSystem.index_nonempty_equiv_nat G F)

/--
This is the generic final step.

If you already have an enumerated family in `Lp` with dense span, no zero
vectors, and a finite-sign bound, this theorem gives an unconditional Schauder
basis whose basis vectors are exactly that family.

The parameter `e` is kept here so this statement matches the later Haar setup.
-/
theorem exists_fullHaarSystem_unconditionalSchauderBasis_of_finiteSignBound
  {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (p : ENNReal)
  [Fact (1 ≤ p)]
    (e : ℕ ≃ F.Index)
    (x : ℕ → FullHaarLpSpace G p)
    (hx_dense : HasDenseSpan (𝕜 := ℝ) x)
    (hx_ne : ∀ n, x n ≠ 0)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_sign : HasFiniteSignBound (𝕜 := ℝ) x C) :
    ∃ b : UnconditionalSchauderBasis ℝ (FullHaarLpSpace G p), b.basis = x := by
  let _ := e
  exact
    UnconditionalCriterion.exists_unconditionalSchauderBasis_of_finiteSignBound
      x hx_dense hx_ne C hC h_sign

/--
    Final result proving that the full Haar system can be rearranged into an unconditional Schauder basis
    for `Lp` when `1 < p < ∞`.

    What this theorem does:
    1. Choose an enumeration of the full Haar indices.
    2. Turn Haar functions into vectors in `Lp`.
    3. Get the finite-sign bound from the Burkholder estimate.
    4. Use density of the Haar span.
    5. Apply the generic criterion above.
-/
theorem exists_fullHaarSystem_unconditionalSchauderBasis_of_BurkholderSignBound
  {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (p : ENNReal)
  [Fact (1 ≤ p)]
    (hp_one : 1 < p)
    (hp_top : p < ⊤) :
    ∃ (e : ℕ ≃ F.Index) (b : UnconditionalSchauderBasis ℝ (FullHaarLpSpace G p)),
      b.basis = (fun n =>
        (FullHaarSystem.memLp_function G F p (e n)).toLp (F.function G (e n))) := by
  let e : ℕ ≃ F.Index := FullHaarSystem.indexEquivNat G F
  let hmem : ∀ i : F.Index, MeasureTheory.MemLp (F.function G i) p G.μ :=
    FullHaarSystem.memLp_function G F p
  have hfin : p ≠ ⊤ := ne_of_lt hp_top
  have hp_one_real : 1 < p.toReal := by
    exact (ENNReal.toReal_lt_toReal (by simp) hfin).2 hp_one
  have hC : 0 ≤ Burkholder.pStar p.toReal - 1 := by
    have hpstar_ge_one : 1 ≤ Burkholder.pStar p.toReal := by
      calc
        1 ≤ p.toReal := le_of_lt hp_one_real
        _ ≤ Burkholder.pStar p.toReal := by
          simpa [Burkholder.pStar, Majorants.pStar, Burkholder.q] using
            (le_max_left p.toReal (Burkholder.q p.toReal))
    linarith
  let x : ℕ → FullHaarLpSpace G p := fun n => (hmem (e n)).toLp (F.function G (e n))
  have hx_ne : ∀ n, x n ≠ 0 := by
    intro n
    simpa [x] using FullHaarSystem.toLp_function_ne_zero G F p hmem (e n)
  -- Finite-sign control comes from the Burkholder estimate proved earlier.
  have h_sign : HasFiniteSignBound (𝕜 := ℝ) x (Burkholder.pStar p.toReal - 1) := by
    simpa [x] using FullHaarSystem.hasFiniteSignBound_of_memLp G F p hp_one hfin hC e hmem
  have hrange : Set.range x = Set.range (fullHaarLpFamily G F p hmem) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e n, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [x, fullHaarLpFamily]⟩
  -- Transfer density from the known dense Haar family to the enumerated family `x`.
  have hx_dense : HasDenseSpan (𝕜 := ℝ) x := by
    rw [HasDenseSpan]
    simpa [x, hrange] using
      (dense_iff_closure_eq.mp (fullHaarFamily_dense G F p hfin hmem))
  rcases
    (exists_fullHaarSystem_unconditionalSchauderBasis_of_finiteSignBound
      G F p e x hx_dense hx_ne (Burkholder.pStar p.toReal - 1) hC h_sign) with ⟨b, hb⟩
  exact ⟨e, b, hb⟩

end UnbalancedHaarWavelet
