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

/-- A generic Fourier superposition of translated lattice boxes is bounded
by a product of the full one-dimensional Weyl suprema. The dimension can be
`2d` or `3d`, and each coordinate can have its own quadratic frequency. -/
theorem norm_weyl_tensor_reduction_le {m : ℕ} {L : ℝ} (hL : 0 < L)
    (F : EuclideanSpace ℝ (Fin m) → ℂ) (hF : Integrable F)
    (s r : Fin m → ℝ) (h : Fin m → ℤ) :
    ‖∑ v : Fin m → ↥(Icc (-⌈L⌉ : ℤ) ⌈L⌉),
      (∏ i, weylCutoff ((v i : ℤ) / L)) *
      (∫ ξ : EuclideanSpace ℝ (Fin m), F ξ * e (∑ i, (ξ i * ((v i : ℤ) + h i)))) *
      e (∑ i, (s i * (((v i : ℤ) : ℝ)+h i)^2 + r i * ((v i : ℤ)+h i)))‖ ≤
      (∫ ξ, ‖F ξ‖) * ∏ i, weylSupremum L (s i) := by
  apply norm_fourier_tensor_reduction_le (κ := fun _ : Fin m => ↥(Icc (-⌈L⌉ : ℤ) ⌈L⌉)) F hF
    (fun i n => weylCutoff ((n : ℤ) / L))
    (fun i n => ((n : ℤ) : ℝ) + h i) s r (fun i => weylSupremum L (s i))
    (fun i => weylSupremum_nonneg hL _)
  intro i ρ
  rw [sum_coe_sort (Icc (-⌈L⌉ : ℤ) ⌈L⌉)
    (fun n => weylCutoff ((n : ℝ)/L) * e (s i * ((n : ℝ)+h i)^2 + ρ*((n : ℝ)+h i)))]
  exact norm_shifted_weyl_factor_le hL (s i) ρ (h i)

end WaveTurbulence.WeylSums
