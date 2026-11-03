/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.DuhamelDerivatives
import Mathlib.Tactic

/-!
# Uniform bounds for cutoff Duhamel derivatives

The primitive bounds remove every dependence on the input frequency from
the output derivative and the frequency-subtracted derivative. These are
the four moment estimates used for DNY21 Lemma 3.1 / TARGET L2365–L2368.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Multiplying a cutoff primitive by an integrable amplitude has a uniform `L¹` bound. -/
theorem integral_norm_mul_duhamelPrimitive_le {a b : ℝ → ℝ}
    (ha : Integrable a) (hb : Integrable b) (σ : ℝ) :
    (∫ t, ‖(a t : ℂ) * duhamelPrimitive b σ t‖) ≤ (∫ t, |a t|) * (∫ t, |b t|) := by
  calc
    _ ≤ ∫ t, |a t| * (∫ u, |b u|) := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        (ha.norm.mul_const _) (ae_of_all _ fun t => ?_)
      change ‖(a t : ℂ) * duhamelPrimitive b σ t‖ ≤ ‖a t‖ * _
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (norm_duhamelPrimitive_le hb σ t) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

/-- Pointwise derivative bound for the output mode, independent of `σ`. -/
theorem norm_deriv_duhamelMode_le {χ : ℝ → ℝ} (hd : Differentiable ℝ χ)
    (hi : Integrable χ) (σ t : ℝ) :
    ‖deriv (duhamelMode χ σ) t‖ ≤ |deriv χ t| * (∫ u, |χ u|) + |χ t| ^ 2 := by
  rw [(hasDerivAt_duhamelMode hd σ t).deriv]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_duhamelPrimitive_le hi σ t) (abs_nonneg _)
  · simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one]
    exact le_rfl

/-- Pointwise remainder bound, independent of `σ`. -/
theorem norm_duhamelRemainder_le {χ : ℝ → ℝ} (h0 : Integrable χ)
    (h1 : Integrable (deriv χ)) (σ t : ℝ) :
    ‖duhamelRemainder χ σ t‖ ≤ |deriv χ t| * (∫ u, |χ u|) +
      |χ t| * |χ 0| + |χ t| * (∫ u, |deriv χ u|) := by
  have ha : ‖((deriv χ t : ℝ) : ℂ) * duhamelPrimitive χ σ t‖ ≤
      |deriv χ t| * (∫ u, |χ u|) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_duhamelPrimitive_le h0 σ t) (abs_nonneg _)
  have hb : ‖(χ t : ℂ) * (χ 0 : ℂ)‖ = |χ t| * |χ 0| := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc : ‖(χ t : ℂ) * duhamelPrimitive (deriv χ) σ t‖ ≤
      |χ t| * (∫ u, |deriv χ u|) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_duhamelPrimitive_le h1 σ t) (abs_nonneg _)
  change ‖((deriv χ t : ℝ) : ℂ) * duhamelPrimitive χ σ t + (χ t : ℂ) * (χ 0 : ℂ) +
    (χ t : ℂ) * duhamelPrimitive (deriv χ) σ t‖ ≤ _
  calc
    _ ≤ (‖((deriv χ t : ℝ) : ℂ) * duhamelPrimitive χ σ t‖ +
      ‖(χ t : ℂ) * (χ 0 : ℂ)‖) + ‖(χ t : ℂ) * duhamelPrimitive (deriv χ) σ t‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add ha hb.le) hc

/-- The derivative of the remainder has the same uniformity. -/
theorem norm_deriv_duhamelRemainder_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h0 : Integrable χ) (h1 : Integrable (deriv χ)) (σ t : ℝ) :
    ‖deriv (duhamelRemainder χ σ) t‖ ≤ |deriv (deriv χ) t| * (∫ u, |χ u|) +
      2 * |χ t| * |deriv χ t| + |deriv χ t| * |χ 0| +
      |deriv χ t| * (∫ u, |deriv χ u|) := by
  rw [(hasDerivAt_duhamelRemainder hχ σ t).deriv]
  have ha : ‖((deriv (deriv χ) t : ℝ) : ℂ) * duhamelPrimitive χ σ t‖ ≤
      |deriv (deriv χ) t| * (∫ u, |χ u|) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_duhamelPrimitive_le h0 σ t) (abs_nonneg _)
  have hb : ‖2 * (χ t : ℂ) * ((deriv χ t : ℝ) : ℂ) *
      (Real.fourierChar (σ * t) : ℂ)‖ = 2 * |χ t| * |deriv χ t| := by
    simp [Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe]
  have hc : ‖((deriv χ t : ℝ) : ℂ) * (χ 0 : ℂ)‖ = |deriv χ t| * |χ 0| := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hd : ‖((deriv χ t : ℝ) : ℂ) * duhamelPrimitive (deriv χ) σ t‖ ≤
      |deriv χ t| * (∫ u, |deriv χ u|) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_duhamelPrimitive_le h1 σ t) (abs_nonneg _)
  calc
    _ ≤ ((‖((deriv (deriv χ) t : ℝ) : ℂ) * duhamelPrimitive χ σ t‖ +
      ‖2 * (χ t : ℂ) * ((deriv χ t : ℝ) : ℂ) * (Real.fourierChar (σ * t) : ℂ)‖) +
      ‖((deriv χ t : ℝ) : ℂ) * (χ 0 : ℂ)‖) +
      ‖((deriv χ t : ℝ) : ℂ) * duhamelPrimitive (deriv χ) σ t‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add ha hb.le) hc.le) hd

/-- A common explicit bound for the four Duhamel Fourier moments.
Only cutoff derivatives through order two occur. -/
@[expose] noncomputable def duhamelMomentConstant (χ : ℝ → ℝ) : ℝ :=
  let a := ∫ t, |χ t|
  let b := ∫ t, |deriv χ t|
  let c := ∫ t, |deriv (deriv χ) t|
  let d := ∫ t, |χ t| ^ 2
  let e := ∫ t, |χ t| * |deriv χ t|
  a ^ 2 + (b * a + d) + (2 * a * b + |χ 0| * a) +
    (c * a + 2 * e + |χ 0| * b + b ^ 2)

/-- The explicit constant in the one-dimensional DNY21 kernel estimate. -/
@[expose] noncomputable def duhamelDecayConstant (χ : ℝ → ℝ) : ℝ :=
  4 * duhamelMomentConstant χ

end WaveTurbulence.Fourier
