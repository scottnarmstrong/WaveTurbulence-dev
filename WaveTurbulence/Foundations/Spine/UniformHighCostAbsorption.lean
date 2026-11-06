/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentAbsorption
/-! Fixed high-order costs are absorbed by the large-torus threshold, uniformly over all stages. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter

theorem eventually_uniform_high_cost_decay (D : ℕ) {a b C : ℝ} (hab : b < a) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ p ≤ D,
      C * (2 : ℝ) ^ (9 * p) * L ^ (-a) ≤ L ^ (-b) := by
  have hh := CountLemmas.eventually_monomial_log_le
    (a := -a) (b := -b) (C := C * (2 : ℝ) ^ (9 * D)) (by linarith) (by positivity) 0
  filter_upwards [hh, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro p hp
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.mul_le_mul_left 9 hp)) hC)
    (Real.rpow_nonneg hL0 _)).trans
  simpa only [pow_zero, mul_one] using hL

end WaveTurbulence.LGSpine
