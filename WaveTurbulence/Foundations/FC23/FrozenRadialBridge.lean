/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.RadialMeasure
public import WaveTurbulence.Frozen.Defs.Chi0
/-! The global radial measure represents the exact D13 cutoff, via its frozen body. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FC23
theorem frozen_chi0_eq (x : ℝ) : WaveTurbulence.chi0 x = Fourier.chi0 x := by
  unfold WaveTurbulence.chi0 Fourier.chi0
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, Real.smoothTransition.one_of_one_le (x := 2 + 2 * x) (by linarith), mul_one]
  · rw [abs_of_nonpos hx, Real.smoothTransition.one_of_one_le (x := 2 - 2 * x) (by linarith), one_mul]
    ring_nf

open Cut2A
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [MeasurableSpace W] [BorelSpace W]

/-- Exact agreement with the frozen cutoff used in prodDyadicCut. -/
theorem frozen_bondMeasure_value (A : W →L[ℝ] V) (b : V) {R : ℝ}
    (hR : 0 < R) (x : W) :
    (bondMeasure A b R).value x = (WaveTurbulence.chi0 (‖A x + b‖ / R) : ℂ) := by
  rw [frozen_chi0_eq]
  exact bondMeasure_value A b hR x
end WaveTurbulence.FC23
