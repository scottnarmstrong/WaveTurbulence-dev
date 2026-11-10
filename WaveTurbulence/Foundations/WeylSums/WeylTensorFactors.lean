/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeylSupremum
public import WaveTurbulence.Foundations.WeylSums.FourierTensorReduction

/-! # Consuming the tensor reduction with the paper's Weyl supremum -/

public section
open Finset MeasureTheory
open scoped BigOperators ContDiff
namespace WaveTurbulence.WeylSums

/-- A translated finite cutoff factor is precisely a smooth Weyl sum,
up to its displayed unit phase. -/
theorem shifted_weyl_factor {L : ℝ} (hL : 0 < L) (s r : ℝ) (h : ℤ) :
    (∑ n ∈ Icc (-⌈L⌉ : ℤ) ⌈L⌉, weylCutoff ((n : ℝ)/L) *
      e (s * ((n : ℝ)+h)^2 + r*((n : ℝ)+h))) =
    e (s*(h : ℝ)^2+r*h) * smoothGaussSum weylCutoff L s (r+2*s*h) 0 := by
  rw [weyl_sum_eq_finite hL, mul_sum]
  apply sum_congr rfl
  intro n hn
  have heq : e (s * ((n : ℝ)+h)^2 + r*((n : ℝ)+h)) =
      e (s*(h : ℝ)^2+r*h) * e (s*(n : ℝ)^2+(r+2*s*h)*n) := by
    rw [← e_add]
    congr 1
    ring
  rw [heq]
  ring

/-- Every finite factor from the standard reduction is bounded by `G(s)`,
uniformly in its translated center and its shifted linear frequency. -/
theorem norm_shifted_weyl_factor_le {L : ℝ} (hL : 0 < L) (s r : ℝ) (h : ℤ) :
    ‖∑ n ∈ Icc (-⌈L⌉ : ℤ) ⌈L⌉, weylCutoff ((n : ℝ)/L) *
      e (s * ((n : ℝ)+h)^2 + r*((n : ℝ)+h))‖ ≤ weylSupremum L s := by
  rw [shifted_weyl_factor hL, norm_mul, norm_e, one_mul]
  exact norm_smoothGaussSum_le_weylSupremum hL s _ 0

end WaveTurbulence.WeylSums
