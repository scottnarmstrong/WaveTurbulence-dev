/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValueOneDim
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Complex test functions in the one-dimensional principal value

DH21 Lemma 6.3 uses complex amplitudes and Fourier phases. We extend the real
cancellation limit to complex test functions by taking real and imaginary parts.
-/

public section

open MeasureTheory Filter Topology

namespace WaveTurbulence.Resonant

/-- Complex-valued finite truncation of `1/u`. -/
@[expose] noncomputable def pvTruncationComplex (χ : ℝ → ℝ) (μ : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ u, (((1 - χ (μ * u)) / u : ℝ) : ℂ) * f u

end WaveTurbulence.Resonant
