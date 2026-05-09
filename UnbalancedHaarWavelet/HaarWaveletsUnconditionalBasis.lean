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
import UnbalancedHaarWavelet.GridDefinition
import UnbalancedHaarWavelet.HaarWavelets_def_Martingale
import UnconditionalSchauderBasis.UnconditionalSchauderBasisNontrivialField

namespace UnbalancedHaarWavelet

open UnconditionalCriterion

abbrev FullHaarLpSpace
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) (p : ENNReal) : Type _ :=
  MeasureTheory.Lp ℝ p G.μ

theorem toLp_finsetSum_const_smul
    {α ι : Type*} [MeasurableSpace α] [DecidableEq ι]
    {μ : MeasureTheory.Measure α} (p : ENNReal)
    (s : Finset ι) (f : ι → α → ℝ)
    (hf : ∀ i, MeasureTheory.MemLp (f i) p μ) (a : ι → ℝ) :
    ∑ i ∈ s, a i • (hf i).toLp (f i)
      =
    ((MeasureTheory.memLp_finsetSum s (fun i _ => (hf i).const_smul (a i)))).toLp
      (fun x => ∑ i ∈ s, a i * f i x) := by
  induction s using Finset.induction_on with
  | empty =>
      symm
      exact MeasureTheory.MemLp.toLp_zero _
  | insert i s hi ih =>
      have hs_mem : MeasureTheory.MemLp (fun x => ∑ j ∈ s, a j * f j x) p μ :=
        MeasureTheory.memLp_finsetSum s (fun j _ => (hf j).const_smul (a j))
      calc
        ∑ j ∈ insert i s, a j • (hf j).toLp (f j)
            = a i • (hf i).toLp (f i) + ∑ j ∈ s, a j • (hf j).toLp (f j) := by
                simp [Finset.sum_insert, hi]
        _ = ((hf i).const_smul (a i)).toLp (a i • f i)
              + hs_mem.toLp (fun x => ∑ j ∈ s, a j * f j x) := by
                rw [ih, ← MeasureTheory.MemLp.toLp_const_smul]
        _ = (((hf i).const_smul (a i)).add hs_mem).toLp
              (fun x => (a i • f i) x + ∑ j ∈ s, a j * f j x) := by
                symm
                exact MeasureTheory.MemLp.toLp_add _ _
        _ = ((MeasureTheory.memLp_finsetSum (insert i s)
              (fun j _ => (hf j).const_smul (a j)))).toLp
              (fun x => ∑ j ∈ insert i s, a j * f j x) := by
          apply MeasureTheory.MemLp.toLp_congr
          exact Filter.Eventually.of_forall (fun x => by
            simp [Finset.sum_insert, hi, smul_eq_mul])

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
This is the abstract `Lp` criterion that should be applied to an enumeration of the full Haar
system once the Burkholder estimate has been converted into a finite-sign bound on the associated
`Lp` vectors.

The intended sequence is `n ↦ [FullHaarSystem.function G F (e n)]` in `MeasureTheory.Lp ℝ p G.μ`.
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
Version of the previous construction specialized to the Burkholder constant.  To obtain the full
Haar unconditional basis theorem, it remains to prove `h_sign` from
`HaarSystem.eLpNorm_finite_wavelet_sum_le_Burkholder_2` for the `Lp` realization of the
enumerated full Haar system.
-/
theorem exists_fullHaarSystem_unconditionalSchauderBasis_of_BurkholderSignBound
  {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (p : ENNReal)
  [Fact (1 ≤ p)]
    (e : ℕ ≃ F.Index)
    (x : ℕ → FullHaarLpSpace G p)
    (hx_dense : HasDenseSpan (𝕜 := ℝ) x)
    (hx_ne : ∀ n, x n ≠ 0)
    (hC : 0 ≤ Burkholder.pStar p.toReal - 1)
    (h_sign : HasFiniteSignBound (𝕜 := ℝ) x (Burkholder.pStar p.toReal - 1)) :
    ∃ b : UnconditionalSchauderBasis ℝ (FullHaarLpSpace G p), b.basis = x := by
  exact
    exists_fullHaarSystem_unconditionalSchauderBasis_of_finiteSignBound
      G F p e x hx_dense hx_ne (Burkholder.pStar p.toReal - 1) hC h_sign

end UnbalancedHaarWavelet
