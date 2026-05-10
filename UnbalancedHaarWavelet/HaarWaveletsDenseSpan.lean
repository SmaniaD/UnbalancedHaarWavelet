import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Data.Finset.Image
import UnbalancedHaarWavelet.HaarWaveletsLinearCombinations


/-!
Density of the span of full Haar family in `Lp`.

The strategy is standard but written in project language:
1. move finite sums into `Lp` cleanly,
2. show indicator-type building blocks belong to the Haar closed span,
3. use measure-theoretic generation and induction,
4. conclude the closed span is all of `Lp`.
-/


namespace UnbalancedHaarWavelet

noncomputable section

open scoped ENNReal symmDiff

abbrev FullHaarLpSpace
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) (p : ENNReal) : Type _ :=
  MeasureTheory.Lp ℝ p G.μ

/-- The full Haar family viewed as vectors in `Lp`. -/
abbrev fullHaarLpFamily
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G)) (p : ENNReal)
    (hmem : ∀ i, MeasureTheory.MemLp (F.function G i) p G.μ) :
    F.Index → FullHaarLpSpace G p :=
  fun i => (hmem i).toLp (F.function G i)

/-- Closed linear span of the full Haar family in `Lp`. -/
abbrev fullHaarClosedSpan
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
  (F : FullHaarSystem (G := G)) (p : ENNReal) [Fact (1 ≤ p)]
    (hmem : ∀ i, MeasureTheory.MemLp (F.function G i) p G.μ) :
    Submodule ℝ (FullHaarLpSpace G p) :=
  (Submodule.span ℝ (Set.range (fullHaarLpFamily G F p hmem))).topologicalClosure

/--
Rewrites a finite linear combination of `toLp` vectors as one `toLp` of the
pointwise finite sum.
-/
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

/--
If a function is in the algebraic span of full Haar functions, then its `Lp`
class lies in the closed Haar span.
-/
theorem mem_fullHaarClosedSpan_of_mem_function_span
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
  (F : FullHaarSystem (G := G))
  (p : ENNReal) [Fact (1 ≤ p)]
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
      ((MeasureTheory.memLp_finsetSum s.attach
        (fun g _ => (hs_mem g.1 g.2).const_smul (a g.1)))).toLp
          (fun x => ∑ g ∈ s.attach, a g.1 * g.1 x) ∈ T := by
    rw [← toLp_finsetSum_const_smul p s.attach (fun g : s => g.1)
      (fun g => hs_mem g.1 g.2) (fun g : s => a g.1)]
    refine Submodule.sum_mem T ?_
    intro g hg
    refine T.smul_mem _ ?_
    rcases hs g.2 with ⟨i, hi⟩
    have htoLp : (hs_mem g.1 g.2).toLp g.1 = (hmem i).toLp (FullHaarSystem.function G F i) := by
      apply MeasureTheory.MemLp.toLp_congr
      exact Filter.Eventually.of_forall (fun x => congrFun hi.symm x)
    rw [htoLp]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hrepr' : (fun x => ∑ g ∈ s.attach, a g.1 * g.1 x) = f := by
    ext x
    calc
      ∑ g ∈ s.attach, a g.1 * g.1 x = ∑ g ∈ s, a g * g x := by
        simpa using (Finset.sum_attach s (fun g => a g * g x))
      _ = f x := by
        simpa [Pi.smul_apply, smul_eq_mul] using congrFun hrepr x
  have hsum_eq :
      ((MeasureTheory.memLp_finsetSum s.attach
        (fun g _ => (hs_mem g.1 g.2).const_smul (a g.1)))).toLp
          (fun x => ∑ g ∈ s.attach, a g.1 * g.1 x) = hf.toLp f := by
    apply MeasureTheory.MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun x => congrFun hrepr' x)
  have : hf.toLp f ∈ T := by
    simpa [hsum_eq] using hsum_mem
  exact (Submodule.le_topologicalClosure T) this

/-- The set of all partition cells across all levels of the grid. -/
def gridGeneratingSets
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) : Set (Set α) :=
  ⋃ n, (G.grid.partitions n : Set (Set α))

/-- Those generating sets form a pi-system. -/
theorem isPiSystem_gridGeneratingSets
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) : IsPiSystem (gridGeneratingSets G) := by
  classical
  intro s hs t ht hst
  rcases Set.mem_iUnion.mp hs with ⟨n, hn⟩
  rcases Set.mem_iUnion.mp ht with ⟨m, hm⟩
  rcases le_total n m with hnm | hmn
  · rcases G.partition_subset_or_disjoint_of_le n m hnm s hn t hm with hsub | hdisj
    · rw [Set.inter_eq_right.2 hsub]
      exact Set.mem_iUnion.mpr ⟨m, hm⟩
    · exfalso
      exact hst.ne_empty (Set.disjoint_iff_inter_eq_empty.mp hdisj.symm)
  · rcases G.partition_subset_or_disjoint_of_le m n hmn t hm s hn with hsub | hdisj
    · rw [Set.inter_eq_left.2 hsub]
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    · exfalso
      exact hst.ne_empty (Set.disjoint_iff_inter_eq_empty.mp hdisj)

  /-- The ambient measurable space is generated by `gridGeneratingSets`. -/
theorem grid_generates_eq_generateFrom_gridGeneratingSets
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) :
    ‹MeasurableSpace α› = MeasurableSpace.generateFrom (gridGeneratingSets G) := by
  calc
    ‹MeasurableSpace α› = ⨆ n, MeasurableSpace.generateFrom (G.grid.partitions n) := by
      simpa using G.grid.generates.symm
    _ = MeasurableSpace.generateFrom (gridGeneratingSets G) := by
      rw [MeasurableSpace.iSup_generateFrom]
      simp [gridGeneratingSets]

/-- Pulls out a scalar from `indicatorConstLp` in `Lp`. -/
lemma indicatorConstLp_eq_smul_indicatorConstLp_one
    {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {p : ENNReal} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) :
    MeasureTheory.indicatorConstLp (μ := μ) p hs hμs c
      = c • MeasureTheory.indicatorConstLp (μ := μ) p hs hμs (1 : ℝ) := by
  ext1
  refine MeasureTheory.indicatorConstLp_coeFn.trans ?_
  have h_smul :=
    MeasureTheory.Lp.coeFn_smul c (MeasureTheory.indicatorConstLp (μ := μ) p hs hμs (1 : ℝ))
  refine Filter.EventuallyEq.trans ?_ h_smul.symm
  refine (@MeasureTheory.indicatorConstLp_coeFn _ _ _ p μ _ s hs hμs (1 : ℝ)).mono ?_
  intro x hx1
  by_cases hxs : x ∈ s
  · simp [hx1, hxs]
  · simp [hx1, hxs]

/-- Indicator of a complement is indicator of universe minus indicator of the set. -/
lemma indicatorConstLp_compl_eq_sub
    {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ] {p : ENNReal}
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) :
    MeasureTheory.indicatorConstLp (μ := μ) p hs.compl (by finiteness) c
      = MeasureTheory.indicatorConstLp (μ := μ) p MeasurableSet.univ (by simp) c
          - MeasureTheory.indicatorConstLp (μ := μ) p hs hμs c := by
  rw [MeasureTheory.indicatorConstLp_univ (μ := μ) (p := p) (c := c)]
  ext1
  refine MeasureTheory.indicatorConstLp_coeFn.trans ?_
  have h_sub :=
    MeasureTheory.Lp.coeFn_sub
      (MeasureTheory.Lp.const p μ c)
      (MeasureTheory.indicatorConstLp (μ := μ) p hs hμs c)
  refine Filter.EventuallyEq.trans ?_ h_sub.symm
  filter_upwards [MeasureTheory.AEEqFun.coeFn_const (α := α) (μ := μ) (b := c),
    MeasureTheory.indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hs) (hμs := hμs)
      (c := c)] with x hxu hxs
  by_cases hmem : x ∈ s
  · simp [hxu, hxs, hmem]
  · simp [hxu, hxs, hmem]

/--
Main induction step for density: indicator-constant vectors belong to the
closed span of the full Haar family.
-/
theorem indicatorConstLp_mem_fullHaarClosedSpan
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (p : ENNReal) [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞)
    (hmem : ∀ i, MeasureTheory.MemLp (F.function G i) p G.μ)
    {s : Set α} (hs : MeasurableSet s) (hμs : G.μ s ≠ ∞) (c : ℝ) :
    MeasureTheory.indicatorConstLp (μ := G.μ) p hs hμs c ∈ fullHaarClosedSpan G F p hmem := by
  classical
  letI : MeasureTheory.IsFiniteMeasure G.μ := G.isFinite
  let M : Submodule ℝ (FullHaarLpSpace G p) := fullHaarClosedSpan G F p hmem
  let C : ∀ t : Set α, MeasurableSet t → Prop :=
    fun t ht =>
      ∀ d : ℝ,
        MeasureTheory.indicatorConstLp (μ := G.μ) p ht ((MeasureTheory.measure_lt_top G.μ t).ne) d ∈ M
  have hempty : C ∅ MeasurableSet.empty := by
    intro d
    simp [C, M]
  have hbasic :
      ∀ t (ht : t ∈ gridGeneratingSets G),
        C t ((grid_generates_eq_generateFrom_gridGeneratingSets G) ▸
          MeasurableSpace.GenerateMeasurable.basic t ht) := by
    intro t ht d
    rcases Set.mem_iUnion.mp ht with ⟨n, hn⟩
    have htm : MeasurableSet t := G.grid.measurable n t hn
    have hμt : G.μ t ≠ ∞ := (MeasureTheory.measure_lt_top G.μ t).ne
    have hspan_one :
        (fun x => Set.indicator t (fun _ => (1 : ℝ)) x)
          ∈ Submodule.span ℝ (Set.range (FullHaarSystem.function G F)) :=
      indicator_partition_mem_span_FullHaarSystem G F t n hn
    have hone : MeasureTheory.indicatorConstLp (μ := G.μ) p htm hμt (1 : ℝ) ∈ M := by
      simpa [MeasureTheory.indicatorConstLp] using
        mem_fullHaarClosedSpan_of_mem_function_span G F p hmem
          (MeasureTheory.memLp_indicator_const p htm (1 : ℝ) (Or.inr hμt)) hspan_one
    rw [indicatorConstLp_eq_smul_indicatorConstLp_one htm hμt d]
    exact M.smul_mem d hone
  have hcompl :
      ∀ t (htm : MeasurableSet t), C t htm → C tᶜ htm.compl := by
    intro t htm ht d
    have huniv : C Set.univ MeasurableSet.univ := by
      have hroot : Set.univ ∈ gridGeneratingSets G := by
        refine Set.mem_iUnion.mpr ⟨0, ?_⟩
        simpa [G.grid.first_partition_eq_univ]
      simpa using hbasic Set.univ hroot
    rw [indicatorConstLp_compl_eq_sub htm ((MeasureTheory.measure_lt_top G.μ t).ne) d]
    exact M.sub_mem (huniv d) (ht d)
  have hiUnion :
      ∀ (f : ℕ → Set α), Pairwise (fun i j => Disjoint (f i) (f j)) → ∀ hfm : ∀ i, MeasurableSet (f i),
        (∀ i, C (f i) (hfm i)) → C (⋃ i, f i) (MeasurableSet.iUnion hfm) := by
    intro f hfd hfm hf c
    let u : ℕ → Set α := fun n => ⋃ i ∈ Finset.range n, f i
    have hu_meas : ∀ n, MeasurableSet (u n) := by
      intro n
      exact Finset.measurableSet_biUnion (Finset.range n) (fun i _ => hfm i)
    have hu_mem : ∀ n, MeasureTheory.indicatorConstLp (μ := G.μ) p (hu_meas n)
        ((MeasureTheory.measure_lt_top G.μ (u n)).ne) c ∈ M := by
      intro n
      induction n with
      | zero =>
          simpa [u, M] using (M.zero_mem : (0 : FullHaarLpSpace G p) ∈ M)
      | succ n ihn =>
          have hdisj_union : Disjoint (u n) (f n) := by
            refine Set.disjoint_left.mpr ?_
            intro x hx_union hx_fn
            simp only [u, Finset.mem_range, Finset.mem_coe, Set.mem_iUnion, exists_prop] at hx_union
            rcases hx_union with ⟨i, hi_lt, hxi⟩
            have hi_ne : i ≠ n := by omega
            exact (Set.disjoint_left.mp (hfd hi_ne) hxi hx_fn).elim
          have hu_succ : u (n + 1) = u n ∪ f n := by
            ext x
            simp only [u, Finset.mem_range, Set.mem_iUnion, exists_prop, Set.mem_union]
            constructor
            · rintro ⟨i, hi_lt, hxi⟩
              by_cases hni : i = n
              · right
                simpa [hni] using hxi
              · left
                exact ⟨i, by omega, hxi⟩
            · rintro (⟨i, hi_lt, hxi⟩ | hxi)
              · exact ⟨i, by omega, hxi⟩
              · exact ⟨n, by omega, hxi⟩
          have h_union_eq :
              MeasureTheory.indicatorConstLp (μ := G.μ) p (hu_meas (n + 1))
                ((MeasureTheory.measure_lt_top G.μ (u (n + 1))).ne) c
                = MeasureTheory.indicatorConstLp (μ := G.μ) p (hu_meas n)
                    ((MeasureTheory.measure_lt_top G.μ (u n)).ne) c
                    + MeasureTheory.indicatorConstLp (μ := G.μ) p (hfm n)
                        ((MeasureTheory.measure_lt_top G.μ (f n)).ne) c := by
            simpa [hu_succ] using
              (MeasureTheory.indicatorConstLp_disjoint_union
                (p := p) (s := u n) (t := f n)
                (hu_meas n) (hfm n)
                ((MeasureTheory.measure_lt_top G.μ (u n)).ne)
                ((MeasureTheory.measure_lt_top G.μ (f n)).ne)
                  hdisj_union c)
          rw [h_union_eq]
          exact M.add_mem ihn (hf n c)
    have hu_subset : ∀ n, u n ⊆ ⋃ i, f i := by
      intro n x hx
      simp only [u, Finset.mem_range, Finset.mem_coe, Set.mem_iUnion, exists_prop] at hx
      rcases hx with ⟨i, -, hxi⟩
      exact Set.mem_iUnion.mpr ⟨i, hxi⟩
    have hsymmDiff : ∀ n, u n ∆ (⋃ i, f i) = ⋃ i ≥ n, f i := by
      intro n
      ext x
      constructor
      · intro hx
        have hx' : x ∈ ⋃ i, f i ∧ x ∉ u n := by
          rcases Set.mem_symmDiff.mp hx with hxu | hxu
          · exfalso
            exact hxu.2 (hu_subset n hxu.1)
          · exact hxu
        rcases Set.mem_iUnion.mp hx'.1 with ⟨i, hxi⟩
        by_cases hi : i < n
        · exfalso
          have hxun : x ∈ u n := by
              exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨by simpa [Finset.mem_range] using hi, hxi⟩⟩
          exact hx'.2 hxun
        · exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Nat.le_of_not_gt hi, hxi⟩⟩
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hi_ge, hxi⟩
        refine Set.mem_symmDiff.mpr ?_
        right
        constructor
        · exact Set.mem_iUnion.2 ⟨i, hxi⟩
        · intro hx_union
          simp only [u, Finset.mem_range, Finset.mem_coe, Set.mem_iUnion, exists_prop] at hx_union
          rcases hx_union with ⟨j, hj_lt, hxj⟩
          have hij : j ≠ i := by omega
          exact (Set.disjoint_left.mp (hfd hij) hxj hxi).elim
    have htail_tendsto :
          Filter.Tendsto (fun n => G.μ (u n ∆ (⋃ i, f i))) Filter.atTop (nhds 0) := by
        have htail_eq :
            (fun n => G.μ (u n ∆ (⋃ i, f i))) = fun n => G.μ (⋃ i ≥ n, f i) := by
          funext n
          rw [hsymmDiff n]
        rw [htail_eq]
        exact MeasureTheory.tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
          (fun i => (hfm i).nullMeasurableSet) hfd
    have hlimit :
          Filter.Tendsto
            (fun n => MeasureTheory.indicatorConstLp (μ := G.μ) p (hu_meas n)
              ((MeasureTheory.measure_lt_top G.μ (u n)).ne) c)
            Filter.atTop
            (nhds (MeasureTheory.indicatorConstLp (μ := G.μ) p (MeasurableSet.iUnion hfm)
              ((MeasureTheory.measure_lt_top G.μ (⋃ i, f i)).ne) c)) := by
      exact MeasureTheory.tendsto_indicatorConstLp_set
        (μ := G.μ) (p := p) (s := ⋃ i, f i)
        (hs := MeasurableSet.iUnion hfm)
        (hμs := (MeasureTheory.measure_lt_top G.μ (⋃ i, f i)).ne)
        (ht := hu_meas)
        (hμt := fun n => (MeasureTheory.measure_lt_top G.μ (u n)).ne)
        hp_top htail_tendsto
    exact (Submodule.isClosed_topologicalClosure
      (Submodule.span ℝ (Set.range (fullHaarLpFamily G F p hmem)))).mem_of_tendsto
        hlimit (Filter.Eventually.of_forall hu_mem)
  have hC : C s hs := by
    refine MeasurableSpace.induction_on_inter
      (grid_generates_eq_generateFrom_gridGeneratingSets G)
      (isPiSystem_gridGeneratingSets G) hempty hbasic hcompl hiUnion s hs
  simpa [M] using hC c

/-- The closed span of the full Haar family is the whole `Lp` space. -/
theorem fullHaarClosedSpan_eq_top
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (p : ENNReal) [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞)
    (hmem : ∀ i, MeasureTheory.MemLp (F.function G i) p G.μ) :
    fullHaarClosedSpan G F p hmem = ⊤ := by
  classical
  let M : Submodule ℝ (FullHaarLpSpace G p) := fullHaarClosedSpan G F p hmem
  apply top_unique
  intro f _
  refine MeasureTheory.Lp.induction (μ := G.μ) (p := p) hp_top (motive := fun g => g ∈ M) ?_ ?_ ?_ f
  · intro c s hs hμs
    simpa [M] using indicatorConstLp_mem_fullHaarClosedSpan G F p hp_top hmem hs hμs.ne c
  · intro f g hf hg _ hfM hgM
    exact M.add_mem hfM hgM
  · simpa [M] using (Submodule.isClosed_topologicalClosure
      (Submodule.span ℝ (Set.range (fullHaarLpFamily G F p hmem))) :
        IsClosed ((fullHaarClosedSpan G F p hmem : Submodule ℝ (FullHaarLpSpace G p)) : Set _))

/-- Equivalent dense-range formulation of `fullHaarClosedSpan_eq_top`. -/
theorem fullHaarFamily_dense
    {α : Type*} [MeasurableSpace α]
    (G : Grid (α := α)) [DecidableEq (Set α)]
    (F : FullHaarSystem (G := G))
    (p : ENNReal) [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞)
    (hmem : ∀ i, MeasureTheory.MemLp (F.function G i) p G.μ) :
    Dense (Submodule.span ℝ (Set.range (fullHaarLpFamily G F p hmem)) :
      Set (FullHaarLpSpace G p)) := by
  rw [dense_iff_closure_eq]
  simpa [fullHaarClosedSpan] using
    congrArg
      (fun S : Submodule ℝ (FullHaarLpSpace G p) => (S : Set (FullHaarLpSpace G p)))
      (fullHaarClosedSpan_eq_top G F p hp_top hmem)





end

end UnbalancedHaarWavelet
