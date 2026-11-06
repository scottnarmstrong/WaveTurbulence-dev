/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedInterpolation
/-! TARGET L2220–2223: interpolation preserves the fixed high-regularity cost outside
all order-dependent powers. This is important because that cost is chosen after delta. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

/-- Fixed outside constants can be shared by the two source estimates without entering
an order-dependent exponential. -/
theorem spliced_fixed_cost_interpolation {z : ℂ} {H η ν d ρ g R n c l u : ℝ}
    (hH : 0 < H) (hν : 0 ≤ ν) (hsmall : 40 * ν ≤ 1 / 100)
    (hcost : 3200 * d * ν ≤ η ^ 6 / 4) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hn : 0 ≤ n) (hl : 0 ≤ l) (hu : u ≤ 0)
    (hc : ‖z‖ ≤ H * Real.exp (n * (c + u / 2) + (-η * g + 80 * d * ρ) * l))
    (hf : ‖z‖ ≤ H * Real.exp (n * (c - 10 * ν * u) +
      (-η ^ 6 * ρ - (R - 1) * (1 / 4 + 1 / 50)) * l)) :
    ‖z‖ ≤ H * Real.exp (n * (c + 10 * ν * u) +
      (-40 * ν * η * g - η ^ 6 * ρ / 2 - (R - 1) * (1 / 4 + 1 / 60)) * l) := by
  have hnorm : ‖z / (H : ℂ)‖ = ‖z‖ / H := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hc' : ‖z / (H : ℂ)‖ ≤ Real.exp
      (n * (c + u / 2) + (-η * g + 80 * d * ρ) * l) := by
    rw [hnorm]
    exact (div_le_iff₀ hH).mpr (by simpa only [mul_comm] using hc)
  have hf' : ‖z / (H : ℂ)‖ ≤ Real.exp (n * (c - 10 * ν * u) +
      (-η ^ 6 * ρ - (R - 1) * (1 / 4 + 1 / 50)) * l) := by
    rw [hnorm]
    exact (div_le_iff₀ hH).mpr (by simpa only [mul_comm] using hf)
  have hb := spliced_interpolation_bound hν hsmall hcost hρ hR hn hl hu hc' hf'
  rw [hnorm] at hb
  exact (div_le_iff₀ hH).mp hb |>.trans_eq (mul_comm _ _)

end WaveTurbulence.LGSpine
