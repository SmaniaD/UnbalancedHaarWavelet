# UnbalancedHaarWavelet

[Read the PDF documentation](docs/Documentation.pdf)

Lean 4 formalization of unbalanced Haar wavelets on general finite measure spaces, following Girardi-Sweldens (1997).

## Main Goal

Given a finite measure space with a nested sequence of finite measurable partitions (a grid), this project formalizes:

1. Binary refinements induced by the grid structure.
2. Unbalanced Haar wavelets associated with branches of those binary refinements.
3. The full Haar system (constant function plus all wavelets).
4. The theorem that this full Haar system is an unconditional Schauder basis of $L^p$, for every $1 < p < \infty$.

## Mathematical Roadmap

The formalization follows this pipeline:

1. **Grid structure**
	 - Nested finite partitions.
	 - Positivity of cell measures.
	 - Measure decrease under refinement.

2. **Induced binary grid**
	 - Existence of binary refinements built from partition children.
	 - Combinatorial branch supports and measurable supports.

3. **Haar wavelet system**
	 - Wavelets defined from branch pairs.
	 - Orthogonality and structural lemmas.

4. **Full Haar system in $L^p$**
	 - Dense span.
	 - Martingale-transform viewpoint.
	 - Unconditional basis result via Burkholder-type inequalities.

## Reference

Maria Girardi and Wim Sweldens,
*A New Class of Unbalanced Haar Wavelets That Form an Unconditional Basis for $L^p$ on General Measure Spaces*,
Journal of Fourier Analysis and Applications, 3(4), 1997.
DOI: [10.1007/BF02649107](https://doi.org/10.1007/BF02649107)

## Repository Structure

- `UnbalancedHaarWavelet/GridDefinition.lean`
	- Nested finite partition sequences and grids.

- `UnbalancedHaarWavelet/HaarWaveletsInducedBinaryGrid.lean`
	- Binary refinements and branch support infrastructure.

- `UnbalancedHaarWavelet/HaarWaveletsDefinition.lean`
	- Haar wavelet and Haar system definitions.

- `UnbalancedHaarWavelet/HaarWaveletsOrthogonality.lean`
	- Orthogonality properties.

- `UnbalancedHaarWavelet/HaarWaveletsLinearCombinations.lean`
	- Finite linear combination lemmas.

- `UnbalancedHaarWavelet/HaarWaveletsDenseSpan.lean`
	- Dense span results.

- `UnbalancedHaarWavelet/HaarWavelets_def_Martingale.lean`
	- Martingale-difference formulation.

- `UnbalancedHaarWavelet/HaarWaveletsUnconditionalBasis.lean`
	- Final unconditional basis theorem in $L^p$.

- `docs/Documentation.tex`
	- Full LaTeX mathematical write-up.



## Status

This repository is part of a broader formalization program around wavelets on general measure spaces, with future targets including Besov-space applications and transfer-operator methods.


## Contributors

Daniel Smania
