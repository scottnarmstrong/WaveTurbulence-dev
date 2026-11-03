/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.ExponentCoordinates
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact B-process scaling

The stationary weight is `N/sqrt(F)` and the dual interval has scale
`Y=F/N`. Applying a `(κ,λ)` estimate there gives the powers of the
B-transform. This algebraic identity does not assert analytic closure.
-/

public section

namespace WaveTurbulence.VdCB

/-- Exact scale conversion from the dual exponent-pair estimate. -/
theorem bProcess_scaling {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y) (κ lam : ℝ) :
    (N / Real.sqrt (N * Y)) * N ^ κ * Y ^ lam =
      Y ^ (lam - 1 / 2) * N ^ (κ + 1 / 2) := by
  have hweight : N / Real.sqrt (N * Y) = N ^ (1 / 2 : ℝ) * Y ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_mul hN.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, div_mul_eq_div_div]
    have heq : N / N ^ (1 / 2 : ℝ) = N ^ (1 / 2 : ℝ) := by
      have hh := Real.rpow_sub hN (1 : ℝ) (1 / 2 : ℝ)
      norm_num only [Real.rpow_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hh
      exact hh.symm
    rw [heq, Real.rpow_neg hY.le, div_eq_mul_inv]
  rw [hweight]
  calc
    _ = (Y ^ lam * Y ^ (-(1 / 2) : ℝ)) * (N ^ κ * N ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hY, ← Real.rpow_add hN]; congr 2

end WaveTurbulence.VdCB
