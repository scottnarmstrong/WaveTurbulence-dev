/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.DuhamelFourier
public import WaveTurbulence.Foundations.Fourier.FrequencyMoments
import Mathlib.Tactic

/-!
# The truncated Duhamel kernel estimate

DNY21 Lemma 3.1 and TARGET L2365–L2368. The four square-free moments
are controlled by cutoff derivatives through order two. The bound is
uniform in both frequencies, including zero input frequency.
-/

public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace WaveTurbulence.Fourier

/-- A common bound for the four integrated Duhamel amplitudes. -/
theorem duhamel_integrated_moments_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (σ : ℝ) :
    (∫ t, ‖duhamelMode χ σ t‖) ≤ duhamelMomentConstant χ ∧
    (∫ t, ‖deriv (duhamelMode χ σ) t‖) ≤ duhamelMomentConstant χ ∧
    (∫ t, ‖duhamelRemainder χ σ t‖) ≤ duhamelMomentConstant χ ∧
    (∫ t, ‖deriv (duhamelRemainder χ σ) t‖) ≤ duhamelMomentConstant χ := by
  let A := (∫ t, |χ t|) ^ 2
  let B := (∫ t, |deriv χ t|) * (∫ t, |χ t|) + ∫ t, |χ t| ^ 2
  let C := 2 * (∫ t, |χ t|) * (∫ t, |deriv χ t|) + |χ 0| * (∫ t, |χ t|)
  let D := (∫ t, |deriv (deriv χ) t|) * (∫ t, |χ t|) +
    2 * (∫ t, |χ t| * |deriv χ t|) + |χ 0| * (∫ t, |deriv χ t|) +
    (∫ t, |deriv χ t|) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hM : duhamelMomentConstant χ = A + B + C + D := rfl
  rw [hM]
  have h0 : (∫ t, ‖duhamelMode χ σ t‖) ≤ A :=
    integral_norm_duhamelMode_le (hχ.continuous.integrable_of_hasCompactSupport hc) σ
  have h1 : (∫ t, ‖deriv (duhamelMode χ σ) t‖) ≤ B :=
    integral_norm_deriv_duhamelMode_le hχ hc σ
  have h2 : (∫ t, ‖duhamelRemainder χ σ t‖) ≤ C :=
    integral_norm_duhamelRemainder_le hχ hc σ
  have h3 : (∫ t, ‖deriv (duhamelRemainder χ σ) t‖) ≤ D :=
    integral_norm_deriv_duhamelRemainder_le hχ hc σ
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Dropping the harmless `2π` from a Fourier derivative multiplier. -/
theorem abs_mul_norm_le_fourier_multiplier (a : ℝ) (z : ℂ) :
    |a| * ‖z‖ ≤ ‖(2 * Real.pi * Complex.I * (a : ℂ)) * z‖ := by
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  have hp : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  nlinarith [mul_nonneg (abs_nonneg a) (norm_nonneg z)]

/-- The one-dimensional cutoff Duhamel kernel has product bracket decay. -/
theorem norm_duhamelKernel_le_brackets {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (ξ σ : ℝ) :
    ‖duhamelKernel χ ξ σ‖ ≤ duhamelDecayConstant χ /
      (Real.sqrt (1 + ξ ^ 2) * Real.sqrt (1 + (ξ - σ) ^ 2)) := by
  obtain ⟨h0, h1, h2, h3⟩ := duhamel_integrated_moments_le hχ hc σ
  apply frequency_decay_two (duhamelKernel χ ξ σ) ξ (ξ - σ) (duhamelMomentConstant χ)
  · exact (Real.norm_fourier_le_integral_norm _ ξ).trans h0
  · calc
      _ ≤ ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) * duhamelKernel χ ξ σ‖ :=
        abs_mul_norm_le_fourier_multiplier _ _
      _ = ‖𝓕 (deriv (duhamelMode χ σ)) ξ‖ := by rw [fourier_deriv_duhamelMode hχ hc]
      _ ≤ _ := (Real.norm_fourier_le_integral_norm _ ξ).trans h1
  · calc
      _ ≤ ‖(2 * Real.pi * Complex.I * ((ξ - σ : ℝ) : ℂ)) * duhamelKernel χ ξ σ‖ :=
        abs_mul_norm_le_fourier_multiplier _ _
      _ = ‖𝓕 (duhamelRemainder χ σ) ξ‖ := by rw [fourier_duhamelRemainder hχ hc]
      _ ≤ _ := (Real.norm_fourier_le_integral_norm _ ξ).trans h2
  · calc
      _ = |ξ| * (|ξ - σ| * ‖duhamelKernel χ ξ σ‖) := by ring
      _ ≤ |ξ| * ‖𝓕 (duhamelRemainder χ σ) ξ‖ := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [fourier_duhamelRemainder hχ hc]
        exact abs_mul_norm_le_fourier_multiplier _ _
      _ ≤ ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) * 𝓕 (duhamelRemainder χ σ) ξ‖ :=
        abs_mul_norm_le_fourier_multiplier _ _
      _ = ‖𝓕 (deriv (duhamelRemainder χ σ)) ξ‖ := by
        rw [fourier_duhamelRemainder hχ hc, fourier_deriv_duhamelRemainder hχ hc]
      _ ≤ _ := (Real.norm_fourier_le_integral_norm _ ξ).trans h3

end WaveTurbulence.Fourier
