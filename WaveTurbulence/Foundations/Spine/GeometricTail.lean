/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! Uniform exponential tails beyond a logarithmic order cutoff. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

/-- A fixed geometric decay absorbs any requested power of L above its logarithmic threshold. -/
theorem geometric_tail_le_rpow {r L B : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ Real.exp (-1)) (hL : 0 < L) (n : ℕ)
    (hn : B * Real.log L ≤ (n : ℝ)) : r ^ n ≤ L ^ (-B) := by
  calc
    r ^ n ≤ Real.exp (-1) ^ n := pow_le_pow_left₀ hr0 hr n
    _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-B * Real.log L) := Real.exp_le_exp.mpr (by linarith)
    _ = L ^ (-B) := by rw [Real.rpow_def_of_pos hL]; congr 1; ring

end WaveTurbulence.LGSpine
