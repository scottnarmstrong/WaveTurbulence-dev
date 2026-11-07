/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Fixed powers of log L, including P7's hE cost, are absorbed after the earlier constants. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open Filter

/-- All constants and the logarithmic exponent are fixed before the L threshold. -/
theorem eventually_constant_log_pow_le (C : ℝ) (A : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ C * Real.log L ^ A ≤ L ^ ε := by
  have hp := (isLittleO_log_rpow_rpow_atTop (A : ℝ) (half_pos hε)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hc := (tendsto_rpow_atTop (half_pos hε)).eventually_ge_atTop C
  filter_upwards [hp, hc, eventually_ge_atTop (1 : ℝ)] with L hlog hconst hL
  refine ⟨hL, ?_⟩
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hL) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ L) _), Real.rpow_natCast] at hlog
  calc
    C * Real.log L ^ A ≤ L ^ (ε / 2) * L ^ (ε / 2) :=
      mul_le_mul hconst hlog (pow_nonneg (Real.log_nonneg hL) _) (by positivity)
    _ = L ^ ε := by
      rw [← Real.rpow_add (by linarith : 0 < L)]
      congr 1
      ring

end WaveTurbulence.FlowerTop
