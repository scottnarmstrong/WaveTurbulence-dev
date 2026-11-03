/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.GaussianLattice
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Poisson summation for damped quadratic phases

Mathlib's complex Gaussian transformation gives exact decay after Poisson
summation. This supplies both the main-term bound and the tails without an
unproved stationary-phase input.
-/

public section

open scoped BigOperators
open Complex

namespace WaveTurbulence.WeylSums

/-- A damped quadratic phase, with Fourier linear frequency `r`. -/
@[expose] noncomputable def gaussianTerm (z : ℂ) (r x : ℝ) : ℂ :=
  Complex.exp (-Real.pi * z * (x : ℂ) ^ 2 + 2 * Real.pi * Complex.I * r * x)

/-- Gaussian-weighted quadratic sum on the integers. -/
@[expose] noncomputable def gaussianTheta (z : ℂ) (r : ℝ) : ℂ :=
  ∑' n : ℤ, gaussianTerm z r n

theorem norm_gaussianTerm (z : ℂ) (r x : ℝ) :
    ‖gaussianTerm z r x‖ = Real.exp (-Real.pi * z.re * x ^ 2) := by
  rw [gaussianTerm, ← Complex.ofReal_pow, Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num

/-- Absolute summability follows directly from the positive damping. -/
theorem summable_gaussianTerm {z : ℂ} (hz : 0 < z.re) (r : ℝ) :
    Summable (fun n : ℤ => gaussianTerm z r n) := by
  apply Summable.of_norm
  have h := summable_gaussian_lattice 0 hz
  apply h.congr
  intro n
  rw [norm_gaussianTerm]
  simp only [sub_zero]
  congr 1
  ring

/-- Positive damping is preserved by inversion. -/
theorem re_inv_pos_of_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < z⁻¹.re := by
  rw [Complex.inv_re]
  apply div_pos hz
  apply Complex.normSq_pos.mpr
  intro h
  have hh : (0 : ℝ) < 0 := by simpa only [h, Complex.zero_re] using hz
  exact (lt_irrefl 0) hh

/-- Exact Poisson transformation of the damped quadratic phase. -/
theorem gaussianTheta_poisson {z : ℂ} (hz : 0 < z.re) (r : ℝ) :
    gaussianTheta z r = (1 / z ^ (1 / 2 : ℂ)) *
      ∑' n : ℤ, Complex.exp (-Real.pi / z * ((n : ℂ) - r) ^ 2) := by
  have h := Complex.tsum_exp_neg_quadratic hz (Complex.I * (r : ℂ))
  have hleft (n : ℤ) : -Real.pi * z * (n : ℂ) ^ 2 +
      2 * Real.pi * (Complex.I * (r : ℂ)) * n =
      -Real.pi * z * (n : ℂ) ^ 2 + 2 * Real.pi * Complex.I * r * n := by ring
  have hright (n : ℤ) : (n : ℂ) + Complex.I * (Complex.I * (r : ℂ)) = (n : ℂ) - r := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, sub_eq_add_neg]
  simpa only [gaussianTheta, gaussianTerm, hleft, hright, Complex.ofReal_intCast] using h

/-- The dual Gaussian has positive real decay coefficient `Re(1/z)`. -/
theorem norm_dual_gaussian (z : ℂ) (r x : ℝ) :
    ‖Complex.exp (-Real.pi / z * ((x : ℂ) - r) ^ 2)‖ =
      Real.exp (-Real.pi * z⁻¹.re * (x - r) ^ 2) := by
  rw [Complex.norm_exp, ← Complex.ofReal_sub, ← Complex.ofReal_pow]
  congr 1
  simp only [div_eq_mul_inv, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Absolute summability of the dual Gaussian. -/
theorem summable_dual_gaussian {z : ℂ} (hz : 0 < z.re) (r : ℝ) :
    Summable (fun n : ℤ => Complex.exp (-Real.pi / z * ((n : ℂ) - r) ^ 2)) := by
  apply Summable.of_norm
  have h := summable_gaussian_lattice r (re_inv_pos_of_re_pos hz)
  apply h.congr
  intro n
  rw [← Complex.ofReal_intCast, norm_dual_gaussian]
  congr 1
  ring

/-- The norm after Poisson summation is bounded by its real Gaussian tails. -/
theorem norm_gaussianTheta_le_dual {z : ℂ} (hz : 0 < z.re) (r : ℝ) :
    ‖gaussianTheta z r‖ ≤ (1 / Real.sqrt ‖z‖) *
      ∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) - r) ^ 2 * z⁻¹.re) := by
  have hnorm : ‖(1 : ℂ) / z ^ (1 / 2 : ℂ)‖ = 1 / Real.sqrt ‖z‖ := by
    rw [norm_div, norm_one]
    congr 1
    have h := Complex.norm_cpow_real z (1 / 2 : ℝ)
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Real.sqrt_eq_rpow] using h
  rw [gaussianTheta_poisson hz r, norm_mul, hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt ‖z‖)
  refine (norm_tsum_le_tsum_norm (summable_dual_gaussian hz r).norm).trans_eq ?_
  apply tsum_congr
  intro n
  rw [← Complex.ofReal_intCast, norm_dual_gaussian]
  congr 1
  ring

end WaveTurbulence.WeylSums
