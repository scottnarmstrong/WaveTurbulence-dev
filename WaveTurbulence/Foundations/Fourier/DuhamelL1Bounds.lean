/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.DuhamelBounds
import Mathlib.Tactic

/-!
# Integrated bounds for the four Duhamel moments

The constants depend only on the cutoff and its first two derivatives.
No input frequency occurs in these estimates.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- The derivative of a smooth compact cutoff is integrable. -/
theorem integrable_deriv_cutoff {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) : Integrable (deriv χ) :=
  (hχ.continuous_deriv (by simp)).integrable_of_hasCompactSupport hc.deriv

/-- The second derivative of a smooth compact cutoff is integrable. -/
theorem integrable_second_deriv_cutoff {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) : Integrable (deriv (deriv χ)) :=
  integrable_deriv_cutoff (contDiff_infty_iff_deriv.mp hχ).2 hc.deriv

/-- Integrated bound for the original Duhamel mode. -/
theorem integral_norm_duhamelMode_le {χ : ℝ → ℝ} (hi : Integrable χ) (σ : ℝ) :
    (∫ t, ‖duhamelMode χ σ t‖) ≤ (∫ t, |χ t|) ^ 2 := by
  simpa only [duhamelMode, pow_two] using integral_norm_mul_duhamelPrimitive_le hi hi σ

/-- The square of a continuous compact cutoff is integrable. -/
theorem integrable_cutoff_abs_sq {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) : Integrable (fun t => |χ t| ^ 2) := by
  have hs : HasCompactSupport (fun t => |χ t| * |χ t|) := hc.abs.mul_right
  have hcont : Continuous (fun t : ℝ => |χ t| * |χ t|) := hχ.abs.mul hχ.abs
  have hi : Integrable (fun t : ℝ => |χ t| * |χ t|) := hcont.integrable_of_hasCompactSupport hs
  simpa only [pow_two] using hi

/-- Integrated bound for the output derivative. -/
theorem integral_norm_deriv_duhamelMode_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (σ : ℝ) :
    (∫ t, ‖deriv (duhamelMode χ σ) t‖) ≤
      (∫ t, |deriv χ t|) * (∫ t, |χ t|) + ∫ t, |χ t| ^ 2 := by
  have hi : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hc
  have hd := integrable_deriv_cutoff hχ hc
  have hs : Integrable (fun t => |χ t| ^ 2) := integrable_cutoff_abs_sq hχ.continuous hc
  calc
    _ ≤ ∫ t, |deriv χ t| * (∫ u, |χ u|) + |χ t| ^ 2 :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        ((hd.abs.mul_const (∫ u, |χ u|)).add hs)
        (ae_of_all _ fun t => norm_deriv_duhamelMode_le (hχ.differentiable (by simp)) hi σ t)
    _ = _ := by
      have h := integral_add (hd.abs.mul_const (∫ u, |χ u|)) hs
      rw [h, integral_mul_const]

/-- Integrated bound for the frequency-subtracted derivative. -/
theorem integral_norm_duhamelRemainder_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (σ : ℝ) :
    (∫ t, ‖duhamelRemainder χ σ t‖) ≤
      2 * (∫ t, |χ t|) * (∫ t, |deriv χ t|) + |χ 0| * (∫ t, |χ t|) := by
  have hi : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hc
  have hd := integrable_deriv_cutoff hχ hc
  calc
    _ ≤ ∫ t, |deriv χ t| * (∫ u, |χ u|) + |χ t| * |χ 0| +
        |χ t| * (∫ u, |deriv χ u|) :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        (((hd.abs.mul_const (∫ u, |χ u|)).add (hi.abs.mul_const |χ 0|)).add (hi.abs.mul_const (∫ u, |deriv χ u|)))
        (ae_of_all _ fun t => norm_duhamelRemainder_le hi hd σ t)
    _ = _ := by
      have h := integral_add ((hd.abs.mul_const (∫ u, |χ u|)).add (hi.abs.mul_const |χ 0|))
        (hi.abs.mul_const (∫ u, |deriv χ u|))
      have h' := integral_add (hd.abs.mul_const (∫ u, |χ u|)) (hi.abs.mul_const |χ 0|)
      simp only [Pi.add_apply] at h h'
      rw [h, h']
      simp only [integral_mul_const]
      ring

/-- Integrated bound for the derivative of the frequency-subtracted derivative. -/
theorem integral_norm_deriv_duhamelRemainder_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (σ : ℝ) :
    (∫ t, ‖deriv (duhamelRemainder χ σ) t‖) ≤
      (∫ t, |deriv (deriv χ) t|) * (∫ t, |χ t|) +
      2 * (∫ t, |χ t| * |deriv χ t|) + |χ 0| * (∫ t, |deriv χ t|) +
      (∫ t, |deriv χ t|) ^ 2 := by
  have hi : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hc
  have hd := integrable_deriv_cutoff hχ hc
  have hdd := integrable_second_deriv_cutoff hχ hc
  have hs : Integrable (fun t => |χ t| * |deriv χ t|) :=
    (hχ.continuous.abs.mul (hχ.continuous_deriv (by simp)).abs).integrable_of_hasCompactSupport
      (hc.abs.mul_right)
  have hs2 : Integrable (fun t => 2 * |χ t| * |deriv χ t|) := by
    simpa only [mul_assoc] using hs.const_mul 2
  calc
    _ ≤ ∫ t, |deriv (deriv χ) t| * (∫ u, |χ u|) +
        2 * |χ t| * |deriv χ t| + |deriv χ t| * |χ 0| +
        |deriv χ t| * (∫ u, |deriv χ u|) :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        ((((hdd.abs.mul_const (∫ u, |χ u|)).add hs2).add (hd.abs.mul_const |χ 0|)).add (hd.abs.mul_const (∫ u, |deriv χ u|)))
        (ae_of_all _ fun t => norm_deriv_duhamelRemainder_le hχ hi hd σ t)
    _ = _ := by
      have h := integral_add (((hdd.abs.mul_const (∫ u, |χ u|)).add hs2).add
        (hd.abs.mul_const |χ 0|)) (hd.abs.mul_const (∫ u, |deriv χ u|))
      have h' := integral_add ((hdd.abs.mul_const (∫ u, |χ u|)).add hs2) (hd.abs.mul_const |χ 0|)
      have h'' := integral_add (hdd.abs.mul_const (∫ u, |χ u|)) hs2
      simp only [Pi.add_apply] at h h' h''
      rw [h, h', h'']
      simp only [integral_mul_const]
      rw [show (fun t => 2 * |χ t| * |deriv χ t|) =
        (fun t => 2 * (|χ t| * |deriv χ t|)) by funext t; ring, integral_const_mul]
      ring

end WaveTurbulence.Fourier
