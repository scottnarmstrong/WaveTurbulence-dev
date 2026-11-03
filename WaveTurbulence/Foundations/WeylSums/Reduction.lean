/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CompactLatticeReduction
public import WaveTurbulence.Foundations.WeylSums.FourierTails
public import WaveTurbulence.Foundations.WeylSums.FourierTranslations
public import WaveTurbulence.Foundations.WeylSums.QuadraticDiagonalization
public import WaveTurbulence.Foundations.WeylSums.WeylSymmetry

/-!
# Shared standard Weyl reductions

DH23 Lemma 6.6 (L1076–L1136) and TARGET (lemcub3), L1560.

* `bilinear_diagonalization` and `cubic_diagonalization` diagonalize the
  quadratic forms and transform all linear frequencies explicitly.
* `exists_bilinear_integer_coordinates` and `exists_cubic_integer_coordinates`
  identify the image lattices; `parity_phase` removes their parity constraints
  by a finite sum of shifted linear frequencies.
* `exists_compact_fourier_representation` decomposes any smooth compact joint
  amplitude, including any compact Gevrey cutoff. `exists_compact_tensor_plateau`
  inserts coordinate cutoffs on an enlarged support box.
* `compact_lattice_weyl_reduction` bounds the resulting joint lattice sum by
  the product of the one-dimensional supremum Weyl sums, uniformly in all
  phase frequencies and integer centers.
* `norm_fourier_truncation_error_le` and `tendsto_fourier_tail_zero` retain the
  error when replacing an integrable Fourier weight by a compact one.

The statements are coordinate-generic: `m=2d` and `m=3d` are the bilinear
and cubic cases. The rescaling `t'=t/L²`, `s'=s/L²` is literal substitution
in the displayed diagonal identities; integration contributes the usual
Jacobian `L⁴` in the cubic application.
-/

public section
