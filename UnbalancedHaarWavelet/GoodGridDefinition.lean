import UnbalancedHaarWavelet.Basic
import LaminarFamiliesMaximalBinaryTrees
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import UnbalancedHaarWavelet.GridDefinition

/-!
Adds quantitative regularity assumptions to a grid.

`GoodGrid` is a `Grid` with two uniform constants that control how cell
measures shrink from parent to child. These bounds are later used when
estimating Haar coefficients.
-/

namespace UnbalancedHaarWavelet

variable {α : Type*} [MeasurableSpace α]

/--
A grid with uniform lower and upper measure-ratio bounds between a parent cell
and any child cell at the next level.
-/
structure GoodGrid extends Grid (α := α) where
  lambda1 : ℝ
  /-- Upper ratio bound (strictly less than 1) -/
  lambda2 : ℝ
  /-- λ₁ is strictly positive -/
  hlambda1_pos : 0 < lambda1
  /-- λ₂ is strictly less than 1 -/
  hlambda2_lt_one : lambda2 < 1
  /-- λ₁ ≤ λ₂ -/
  hlambda1_le_lambda2 : lambda1 ≤ lambda2
  /-- Each child cell's measure is at least λ₁ times its parent's measure -/
  ratio_lower : ∀ (n : ℕ) (s t : Set α),
      s ∈ grid.partitions (n + 1) → t ∈ grid.partitions n → s ⊆ t →
      ENNReal.ofReal lambda1 * μ t ≤ μ s
  /-- Each child cell's measure is at most λ₂ times its parent's measure -/
  ratio_upper : ∀ (n : ℕ) (s t : Set α),
      s ∈ grid.partitions (n + 1) → t ∈ grid.partitions n → s ⊆ t →
      μ s ≤ ENNReal.ofReal lambda2 * μ t

end UnbalancedHaarWavelet
