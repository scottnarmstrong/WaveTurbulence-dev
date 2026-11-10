/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeWeights
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-!
# Hölder interpolation of time Fourier norms

TARGET `(normX1)`: logarithmic convexity in the time regularity exponent.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

@[fun_prop] theorem timeFourier_continuous {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) : Continuous (timeFourier f) := by
  apply VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar _ hf
  change Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => ∑ j, p.1 j * p.2 j)
  fun_prop

end WaveTurbulence.Fourier
