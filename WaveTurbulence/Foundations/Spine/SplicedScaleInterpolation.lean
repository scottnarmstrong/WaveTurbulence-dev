/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedFixedCostInterpolation
public import WaveTurbulence.Foundations.Spine.SourceScaleExponential
/-! Literal source scale products in finalsbest1 and finalsbest2 imply finalproof1. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

/-- TARGET L2220–2223, keeping the outside high-regularity cost fixed. -/
theorem spliced_scale_interpolation {z : ℂ} {C H δ L η ν d ρ g R : ℝ} (n : ℕ)
    (hC : 0 < C) (hH : 0 < H) (hCH : C ≤ H)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 1 ≤ L)
    (hν : 0 ≤ ν) (hsmall : 40 * ν ≤ 1 / 100)
    (hcost : 3200 * d * ν ≤ η ^ 6 / 4) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hc : ‖z‖ ≤ H * (C * Real.sqrt δ) ^ n * L ^ (-η * g + 80 * d * ρ))
    (hf : ‖z‖ ≤ C * (C * δ ^ (-10 * ν)) ^ n *
      L ^ (-η ^ 6 * ρ) * L ^ (-(R - 1) * (1 / 4 + 1 / 50))) :
    ‖z‖ ≤ H * Real.exp ((n : ℝ) * (Real.log C + 10 * ν * Real.log δ) +
      (-40 * ν * η * g - η ^ 6 * ρ / 2 - (R - 1) * (1 / 4 + 1 / 60)) * Real.log L) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hc' : ‖z‖ ≤ H * Real.exp ((n : ℝ) * (Real.log C + Real.log δ / 2) +
      (-η * g + 80 * d * ρ) * Real.log L) := by
    rw [Real.sqrt_eq_rpow] at hc
    rw [mul_assoc, source_scale_eq_exp hC hδ hL0] at hc
    convert hc using 1 <;> ring
  have hf' : ‖z‖ ≤ H * Real.exp ((n : ℝ) * (Real.log C - 10 * ν * Real.log δ) +
      (-η ^ 6 * ρ - (R - 1) * (1 / 4 + 1 / 50)) * Real.log L) := by
    have heq : C * (C * δ ^ (-10 * ν)) ^ n * L ^ (-η ^ 6 * ρ) *
        L ^ (-(R - 1) * (1 / 4 + 1 / 50)) =
        C * Real.exp ((n : ℝ) * (Real.log C - 10 * ν * Real.log δ) +
          (-η ^ 6 * ρ - (R - 1) * (1 / 4 + 1 / 50)) * Real.log L) := by
      rw [mul_assoc, mul_assoc, ← Real.rpow_add hL0,
        source_scale_eq_exp hC hδ hL0]
      congr 2 <;> ring
    rw [heq] at hf
    exact hf.trans (mul_le_mul_of_nonneg_right hCH (Real.exp_pos _).le)
  exact spliced_fixed_cost_interpolation hH hν hsmall hcost hρ hR
    (Nat.cast_nonneg n) (Real.log_nonneg hL) (Real.log_nonpos hδ.le hδ1) hc' hf'

end WaveTurbulence.LGSpine
