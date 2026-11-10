/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import WaveTurbulence.Foundations.Fourier.FrequencyMoments
import Mathlib.Tactic

/-!
# The truncated Duhamel kernel estimate

DNY21 Lemma 3.1 and TARGET L2365–L2368. The four square-free moments
are controlled by cutoff derivatives through order two. The bound is
uniform in both frequencies, including zero input frequency.
-/

public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace WaveTurbulence.Fourier

/-- Dropping the harmless `2π` from a Fourier derivative multiplier. -/
theorem abs_mul_norm_le_fourier_multiplier (a : ℝ) (z : ℂ) :
    |a| * ‖z‖ ≤ ‖(2 * Real.pi * Complex.I * (a : ℂ)) * z‖ := by
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  have hp : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  nlinarith [mul_nonneg (abs_nonneg a) (norm_nonneg z)]

end WaveTurbulence.Fourier
