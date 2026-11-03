/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.GaussianPairing
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The oscillatory boundary of Gaussian pairing

Schwartz amplitudes permit dominated convergence to the imaginary
Gaussian parameter. No absolute integrability of the bare Fresnel
exponential is asserted or used.
-/

public section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap Topology

namespace WaveTurbulence.VdCB

/-- A complex Gaussian has norm at most one in the closed right half-plane. -/
theorem norm_gaussian_le_one {b : ℂ} (hb : 0 ≤ b.re) (x : ℝ) :
    ‖Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)‖ ≤ 1 := by
  have hh := norm_cexp_neg_mul_sq ((Real.pi : ℂ) * b) x
  have heq : ‖Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)‖ = Real.exp (-(Real.pi * b.re) * x ^ 2) := by
    simpa only [neg_mul, mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hh
  rw [heq]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg Real.pi_pos.le hb)) (sq_nonneg x))

/-- Dominated convergence for Gaussian pairing with a Schwartz amplitude. -/
theorem tendsto_integral_schwartz_mul_gaussian (a : 𝓢(ℝ, ℂ)) {B : ℕ → ℂ} {b : ℂ}
    (hB : Tendsto B atTop (𝓝 b)) (hRe : ∀ n, 0 ≤ (B n).re) :
    Tendsto (fun n => ∫ x : ℝ, a x * Complex.exp (-Real.pi * B n * (x : ℂ) ^ 2)) atTop
      (𝓝 (∫ x : ℝ, a x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2))) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖a x‖)
  · intro n
    have hc : Continuous (fun x : ℝ => a x * Complex.exp (-Real.pi * B n * (x : ℂ) ^ 2)) := by fun_prop
    exact hc.aestronglyMeasurable
  · exact a.integrable.norm
  · intro n
    exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (norm_gaussian_le_one (hRe n) x) (norm_nonneg _)).trans_eq (mul_one _)
  · exact Filter.Eventually.of_forall fun x => by
      have he := Complex.continuous_exp.tendsto (-Real.pi * b * (x : ℂ) ^ 2)
      exact tendsto_const_nhds.mul (he.comp ((hB.const_mul (-(Real.pi : ℂ))).mul_const ((x : ℂ) ^ 2)))

/-- The Gaussian pairing identity extends to nonzero boundary parameters
in the slit plane; in particular to negative imaginary parameters. -/
theorem integral_schwartz_mul_gaussian_closed (a : 𝓢(ℝ, ℂ)) {b : ℂ}
    (hb : 0 ≤ b.re) (hbs : b ∈ Complex.slitPlane) :
    (∫ x : ℝ, a x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2)) =
      1 / b ^ (1 / 2 : ℂ) *
        ∫ ξ : ℝ, 𝓕 a ξ * Complex.exp (-Real.pi / b * (ξ : ℂ) ^ 2) := by
  let B : ℕ → ℂ := fun n => b + (1 / ((n : ℝ) + 1) : ℝ)
  have hB : Tendsto B atTop (𝓝 b) := by
    have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
    simpa only [B, Function.comp_apply, Complex.ofReal_zero, add_zero] using tendsto_const_nhds.add hh
  have hpos (n : ℕ) : 0 < (B n).re := by
    dsimp only [B]
    rw [Complex.add_re, Complex.ofReal_re]
    exact add_pos_of_nonneg_of_pos hb (by positivity)
  have hne : b ≠ 0 := Complex.slitPlane_ne_zero hbs
  have hL := tendsto_integral_schwartz_mul_gaussian a hB (fun n => (hpos n).le)
  have hRi : Tendsto (fun n => (B n)⁻¹) atTop (𝓝 b⁻¹) := hB.inv₀ hne
  have hR := tendsto_integral_schwartz_mul_gaussian (𝓕 a) hRi (fun n => by
    rw [Complex.inv_re]
    exact div_nonneg (hpos n).le (Complex.normSq_nonneg _))
  have hp := (continuousAt_cpow_const (b := (1 / 2 : ℂ)) hbs).tendsto.comp hB
  have hpn : b ^ (1 / 2 : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hne)
  have hP := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).div hp hpn
  have hPR := hP.mul hR
  have heq (n : ℕ) := integral_schwartz_mul_gaussian a (hpos n)
  have hsame := hL.congr (fun n => heq n)
  apply tendsto_nhds_unique hsame
  simpa only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply, Function.comp_apply] using hPR

end WaveTurbulence.VdCB
