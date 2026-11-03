/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.ScalarCutoff
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Fourier mass on affine scalar lines

The rank-two stationary-phase step of TARGET `lemcubic0` uses the exact
change of variables along either of its two bilinear directions.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory
open scoped FourierTransform

/-- Absolute Fourier mass after an invertible affine scalar substitution. -/
theorem integral_norm_fourier_affine (f : ScalarCutoff) (b a : ℝ) :
    (∫ y : ℝ, ‖𝓕 (f : ℝ → ℂ) (a + b * y)‖) =
      |b|⁻¹ * ∫ u : ℝ, ‖𝓕 (f : ℝ → ℂ) u‖ := by
  have he : (fun y : ℝ => ‖𝓕 (f : ℝ → ℂ) (a + b * y)‖) =
      fun y => (fun u => ‖𝓕 (f : ℝ → ℂ) (a + u)‖) (b * y) := rfl
  rw [he, Measure.integral_comp_mul_left (fun u : ℝ => ‖𝓕 (f : ℝ → ℂ) (a + u)‖) b,
    integral_add_left_eq_self (fun u : ℝ => ‖𝓕 (f : ℝ → ℂ) u‖) a]
  simp only [abs_inv, smul_eq_mul]

/-- Integrability in the same affine substitution. -/
theorem integrable_norm_fourier_affine (f : ScalarCutoff) {b : ℝ} (hb : b ≠ 0) (a : ℝ) :
    Integrable (fun y : ℝ => ‖𝓕 (f : ℝ → ℂ) (a + b * y)‖) := by
  have hf : Integrable (fun u => ‖𝓕 (f : ℝ → ℂ) u‖) := (𝓕 f.schwartz).integrable.norm
  exact (hf.comp_add_left a).comp_mul_left' hb

/-- A bounded factor costs only its supremum and reciprocal frequency speed. -/
theorem integral_cutoff_fourier_affine_le (f g : ScalarCutoff) {b : ℝ}
    (hb : b ≠ 0) (a : ℝ) :
    (∫ y : ℝ, ‖g y‖ * ‖𝓕 (f : ℝ → ℂ) (a + b * y)‖) ≤
      SchwartzMap.seminorm ℂ 0 0 g.schwartz *
        (|b|⁻¹ * ∫ u : ℝ, ‖𝓕 (f : ℝ → ℂ) u‖) := by
  have hf := integrable_norm_fourier_affine f hb a
  have hbnd (y : ℝ) : ‖g y‖ * ‖𝓕 (f : ℝ → ℂ) (a + b * y)‖ ≤
      SchwartzMap.seminorm ℂ 0 0 g.schwartz * ‖𝓕 (f : ℝ → ℂ) (a + b * y)‖ :=
    mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ g.schwartz y) (norm_nonneg _)
  apply (integral_mono_of_nonneg (ae_of_all _ (fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (hf.const_mul _) (ae_of_all _ hbnd)).trans_eq
  rw [integral_const_mul, integral_norm_fourier_affine f b]

end WaveTurbulence.LemLin
