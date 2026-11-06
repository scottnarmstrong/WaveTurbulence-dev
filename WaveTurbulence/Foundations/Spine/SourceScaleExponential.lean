/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! Exact logarithmic normalization of source scale products. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

 theorem source_scale_eq_exp {C δ L : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hL : 0 < L)
    (n : ℕ) (b c : ℝ) :
    (C * δ ^ b) ^ n * L ^ c =
      Real.exp ((n : ℝ) * (Real.log C + b * Real.log δ) + c * Real.log L) := by
  have hp : 0 < (C * δ ^ b) ^ n * L ^ c := by positivity
  rw [← Real.exp_log hp]
  congr 1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul hC.ne' (Real.rpow_pos_of_pos hδ _).ne', Real.log_rpow hδ, Real.log_rpow hL]

end WaveTurbulence.LGSpine
