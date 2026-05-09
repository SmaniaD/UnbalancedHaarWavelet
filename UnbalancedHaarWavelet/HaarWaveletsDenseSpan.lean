import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Data.Finset.Image
import UnbalancedHaarWavelet.HaarWaveletsLinearCombinations
import UnconditionalSchauderBasis.UnconditionalSchauderBasisNontrivialField


namespace UnbalancedHaarWavelet

abbrev FullHaarLpSpace
		{α : Type*} [MeasurableSpace α]
		(G : Grid (α := α)) (p : ENNReal) : Type _ :=
	MeasureTheory.Lp ℝ p G.μ

abbrev fullHaarLpFamily
		{α : Type*} [MeasurableSpace α]
		(G : Grid (α := α)) [DecidableEq (Set α)]
		(F : FullHaarSystem (G := G)) (p : ENNReal)
		(hmem : ∀ i, MeasureTheory.MemLp (F.function G i) p G.μ) :
		F.Index → FullHaarLpSpace G p :=
	fun i => (hmem i).toLp (F.function G i)

abbrev fullHaarClosedSpan
		{α : Type*} [MeasurableSpace α]
		(G : Grid (α := α)) [DecidableEq (Set α)]
		(F : FullHaarSystem (G := G)) (p : ENNReal)
		(hmem : ∀ i, MeasureTheory.MemLp (F.function G i) p G.μ) :
		Submodule ℝ (FullHaarLpSpace G p) :=
	(Submodule.span ℝ (Set.range (fullHaarLpFamily G F p hmem))).topologicalClosure

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

theorem mem_fullHaarClosedSpan_of_mem_function_span
		{α : Type*} [MeasurableSpace α]
		(G : Grid (α := α)) [DecidableEq (Set α)]
		(F : FullHaarSystem (G := G))
		(p : ENNReal)
		(hmem : ∀ i, MeasureTheory.MemLp (F.function G i) p G.μ)
		{f : α → ℝ} (hf : MeasureTheory.MemLp f p G.μ)
		(hspan : f ∈ Submodule.span ℝ (Set.range (FullHaarSystem.function G F))) :
		hf.toLp f ∈ fullHaarClosedSpan G F p hmem := by
	classical
	let T : Submodule ℝ (FullHaarLpSpace G p) :=
		Submodule.span ℝ (Set.range (fullHaarLpFamily G F p hmem))
	rcases (Submodule.mem_span_iff_exists_finset_subset).mp hspan with ⟨a, s, hs, -, hrepr⟩
	have hs_mem : ∀ g ∈ s, MeasureTheory.MemLp g p G.μ := by
		intro g hg
		rcases hs hg with ⟨i, rfl⟩
		exact hmem i
	have hsum_mem :
			((MeasureTheory.memLp_finsetSum s (fun g hg => (hs_mem g hg).const_smul (a g)))).toLp
					(fun x => ∑ g ∈ s, a g * g x) ∈ T := by
		rw [← toLp_finsetSum_const_smul p s (fun g => g) (fun g => hs_mem g (by simp)) a]
		refine Submodule.sum_mem T ?_
		intro g hg
		refine T.smul_mem _ ?_
		rcases hs hg with ⟨i, rfl⟩
		exact Submodule.subset_span ⟨i, rfl⟩
	have hrepr' : (fun x => ∑ g ∈ s, a g * g x) = f := by
		ext x
		simpa [Pi.smul_apply, smul_eq_mul] using congrFun hrepr x
	have hsum_eq :
			((MeasureTheory.memLp_finsetSum s (fun g hg => (hs_mem g hg).const_smul (a g)))).toLp
					(fun x => ∑ g ∈ s, a g * g x) = hf.toLp f := by
		apply MeasureTheory.MemLp.toLp_congr
		exact Filter.Eventually.of_forall hrepr'
	have : hf.toLp f ∈ T := by
		simpa [hsum_eq] using hsum_mem
	exact (Submodule.le_topologicalClosure T) this





end UnbalancedHaarWavelet
