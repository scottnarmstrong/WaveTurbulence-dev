/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.GaussianCompletion
import Mathlib.Tactic

/-!
# The damping parameter at major-arc scale

For the Gaussian cutoff `exp(-π(x/L)²)`, the complex damping is
`L⁻² - 2iβ`. Rational approximation makes the merged dual lattice decay
coefficient at least `1/5`, giving a log-free estimate.
-/

public section

namespace WaveTurbulence.WeylSums

/-- Complex Gaussian damping for a real quadratic frequency. -/
@[expose] noncomputable def gaussianDamping (L β : ℝ) : ℂ :=
  (((L ^ 2)⁻¹ : ℝ) : ℂ) - 2 * Complex.I * β

@[simp] theorem gaussianDamping_re (L β : ℝ) : (gaussianDamping L β).re = (L ^ 2)⁻¹ := by
  rw [gaussianDamping, Complex.sub_re, Complex.ofReal_re]
  simp [Complex.mul_re, Complex.mul_im]

@[simp] theorem gaussianDamping_im (L β : ℝ) : (gaussianDamping L β).im = -2 * β := by
  rw [gaussianDamping, Complex.sub_im, Complex.ofReal_im]
  simp [Complex.mul_im, Complex.mul_re]

theorem gaussianDamping_normSq (L β : ℝ) :
    Complex.normSq (gaussianDamping L β) = ((L ^ 2)⁻¹) ^ 2 + 4 * β ^ 2 := by
  rw [Complex.normSq_apply, gaussianDamping_re, gaussianDamping_im]
  ring

theorem gaussianDamping_re_pos {L : ℝ} (hL : 0 < L) (β : ℝ) :
    0 < (gaussianDamping L β).re := by
  rw [gaussianDamping_re]
  positivity

/-- The merged Poisson lattice has a fixed positive decay coefficient. -/
theorem gaussianDamping_decay {L Q β : ℝ} (hL : 0 < L) (hQ : 0 < Q) (hQL : Q ≤ L)
    (happrox : |β| ≤ 1 / (Q * L)) :
    (1 : ℝ) / 5 ≤ (gaussianDamping L β)⁻¹.re / Q ^ 2 := by
  have hβ : |β| * Q * L ≤ 1 := by
    have hh := (le_div_iff₀ (mul_pos hQ hL)).mp happrox
    simpa only [mul_assoc] using hh
  have hβ0 : 0 ≤ |β| * Q * L := by positivity
  have hβsq : β ^ 2 * Q ^ 2 * L ^ 2 ≤ 1 := by
    have hh := pow_le_pow_left₀ hβ0 hβ 2
    simpa only [mul_pow, sq_abs, one_pow] using hh
  have hQLsq : Q ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hQ.le hQL 2
  have hβL := mul_le_mul_of_nonneg_right hβsq (sq_nonneg L)
  have hden : 0 < Q ^ 2 * (1 + 4 * β ^ 2 * L ^ 4) := by positivity
  have hnorm : 0 < ((L ^ 2)⁻¹) ^ 2 + 4 * β ^ 2 := by positivity
  have heq : (gaussianDamping L β)⁻¹.re / Q ^ 2 =
      L ^ 2 / (Q ^ 2 * (1 + 4 * β ^ 2 * L ^ 4)) := by
    rw [Complex.inv_re, gaussianDamping_re, gaussianDamping_normSq]
    field_simp
  rw [heq]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hden).mpr
  nlinarith only [hβL, hQLsq]

/-- The Gaussian Fourier prefactor has the required major-arc denominator. -/
theorem gaussianDamping_prefactor_le {L : ℝ} (hL : 0 < L) (β : ℝ) :
    1 / Real.sqrt ‖gaussianDamping L β‖ ≤
      2 * L / (1 + L * Real.sqrt |β|) := by
  have hz := gaussianDamping_re_pos hL β
  have hnpos : 0 < ‖gaussianDamping L β‖ := by
    exact lt_of_lt_of_le hz (Complex.re_le_norm _)
  have hroot : 0 < Real.sqrt ‖gaussianDamping L β‖ := Real.sqrt_pos.mpr hnpos
  have hreal : (L ^ 2)⁻¹ ≤ ‖gaussianDamping L β‖ := by
    simpa only [gaussianDamping_re] using Complex.re_le_norm (gaussianDamping L β)
  have hs := Real.sqrt_le_sqrt hreal
  rw [Real.sqrt_inv, Real.sqrt_sq hL.le] at hs
  have h₁ : 1 ≤ L * Real.sqrt ‖gaussianDamping L β‖ := by
    have hh := (div_le_iff₀ hL).mp (show (1 : ℝ) / L ≤ Real.sqrt ‖gaussianDamping L β‖ by
      simpa only [one_div] using hs)
    simpa only [mul_comm] using hh
  have him := Complex.abs_im_le_norm (gaussianDamping L β)
  rw [gaussianDamping_im, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at him
  have habs : |β| ≤ ‖gaussianDamping L β‖ := by linarith only [him, abs_nonneg β]
  have h₂ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt habs) hL.le
  apply (div_le_div_iff₀ hroot (by positivity : 0 < 1 + L * Real.sqrt |β|)).mpr
  linarith only [h₁, h₂]

/-- Splitting the damping into its rational and small-error parts. -/
theorem gaussianDamping_split (L s t : ℝ) :
    gaussianDamping L s = gaussianDamping L (s - t) - 2 * Complex.I * t := by
  unfold gaussianDamping
  push_cast
  ring

end WaveTurbulence.WeylSums
