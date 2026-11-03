/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.PoissonLattice
public import WaveTurbulence.Foundations.Fourier.PoissonBlocks
public import WaveTurbulence.Foundations.Fourier.CutoffPhase
public import WaveTurbulence.Foundations.Fourier.HausdorffYoungLp
public import WaveTurbulence.Foundations.Fourier.DoubleDuhamelModes
public import WaveTurbulence.Foundations.Fourier.DuhamelSuperposition
public import WaveTurbulence.Foundations.Fourier.TimeIntegralBounds
public import WaveTurbulence.Foundations.Fourier.PhaseTimeIntegralBounds

/-!
# Poisson summation, phase bounds, Hausdorff–Young, and time integration

Entry point for packet AN-PHASE-HY. Source-facing results:

* `poisson_scaled`, `poisson_scaled_coordinates`, `poisson_scaled_smooth_compact`,
  and `poisson_scaled_blocks`: TARGET L1035, L1541, L1575.
* `chi0_nonstationary_phase` and `chi0_bilinear_stationary_phase`: TARGET L966–L968.
* `timeFourier_hausdorffYoung`, `hausdorffYoungLp`, and `hausdorffYoungLp_norm_le`:
  norm-one Hausdorff–Young on the full exponent range `1 ≤ p ≤ 2`.
* `norm_doubleDuhamelKernel_le`: DNY21 Lemma 3.1, in the tensor form used
  at TARGET L2365–L2368. The literal operators act on Fourier modes as
  proved in `DoubleDuhamelModes`; scalar Schwartz superposition is proved
  in `DuhamelSuperposition`.
* `exists_cutoff_timeIntegral_bounds`: TARGET Lemma A.2, with arbitrary
  complex inputs and the explicit small-parameter range `0 < η ≤ 1/3`.
* `exists_cutoff_phase_mixedNorm_bound`: TARGET Lemma A.3, with the
  owner-approved smooth compact time slices and arbitrary momentum phases.

The source conventions and proof repairs are recorded at each result.
-/

public section
