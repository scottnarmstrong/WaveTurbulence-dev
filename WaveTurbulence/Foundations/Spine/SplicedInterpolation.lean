/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Interpolation
/-! TARGET L2220–2223: the precise 40ν interpolation yields finalsbest1 + finalsbest2 → finalproof1. -/
public section
namespace WaveTurbulence.LGSpine

/-- The cost of the coarse estimate's `80d rho` term fits into half the counting gain. -/
theorem spliced_L_exponent_le {η ν d ρ g R : ℝ}
    (hν : 0 ≤ ν) (he : 0 ≤ η ^ 6) (hsmall : 40 * ν ≤ 1 / 100)
    (hcost : 3200 * d * ν ≤ η ^ 6 / 4) (hρ : 0 ≤ ρ) (hR : 1 ≤ R) :
    (40 * ν) * (-η * g + 80 * d * ρ) +
      (1 - 40 * ν) * (-η ^ 6 * ρ - (R - 1) * (1 / 4 + 1 / 50)) ≤
      -40 * ν * η * g - η ^ 6 * ρ / 2 - (R - 1) * (1 / 4 + 1 / 60) := by
  have hη : η ^ 6 * (40 * ν) ≤ η ^ 6 / 4 := by
    have hh := mul_le_mul_of_nonneg_left hsmall he
    linarith
  have hcoef : (40 * ν) * (80 * d) - (1 - 40 * ν) * η ^ 6 ≤ -η ^ 6 / 2 := by
    nlinarith
  have hroot : (1 / 4 + 1 / 60 : ℝ) ≤ (1 - 40 * ν) * (1 / 4 + 1 / 50) := by linarith
  have hρbound := mul_le_mul_of_nonneg_right hcoef hρ
  have hRbound := mul_le_mul_of_nonneg_right hroot (sub_nonneg.mpr hR)
  nlinarith

/-- The same interpolation produces at least the desired positive delta exponent. -/
theorem spliced_delta_exponent_ge (ν : ℝ) :
    10 * ν ≤ (40 * ν) * (1 / 2) + (1 - 40 * ν) * (-10 * ν) := by
  nlinarith [sq_nonneg ν]

/-- The actual scalar interpolation step; logarithms isolate all constant and scale bookkeeping. -/
theorem spliced_interpolation_bound {z : ℂ} {η ν d ρ g R n c l u : ℝ}
    (hν : 0 ≤ ν) (hsmall : 40 * ν ≤ 1 / 100) (hcost : 3200 * d * ν ≤ η ^ 6 / 4)
    (hρ : 0 ≤ ρ) (hR : 1 ≤ R) (hn : 0 ≤ n) (hl : 0 ≤ l) (hu : u ≤ 0)
    (hcoarse : ‖z‖ ≤ Real.exp (n * (c + u / 2) + (-η * g + 80 * d * ρ) * l))
    (hcount : ‖z‖ ≤ Real.exp (n * (c - 10 * ν * u) +
      (-η ^ 6 * ρ - (R - 1) * (1 / 4 + 1 / 50)) * l)) :
    ‖z‖ ≤ Real.exp (n * (c + 10 * ν * u) +
      (-40 * ν * η * g - η ^ 6 * ρ / 2 - (R - 1) * (1 / 4 + 1 / 60)) * l) := by
  have haWeight0 : 0 ≤ 40 * ν := mul_nonneg (by norm_num) hν
  have haWeight1 : 40 * ν ≤ 1 := by linarith
  apply (norm_le_exp_interpolation hcoarse hcount haWeight0 haWeight1).trans
  apply Real.exp_le_exp.mpr
  have hL := mul_le_mul_of_nonneg_right
    (spliced_L_exponent_le (g := g) hν (by positivity : 0 ≤ η ^ 6) hsmall hcost hρ hR) hl
  have hδ := mul_le_mul_of_nonpos_right (spliced_delta_exponent_ge ν) hu
  have hδn := mul_le_mul_of_nonneg_left hδ hn
  nlinarith

end WaveTurbulence.LGSpine
