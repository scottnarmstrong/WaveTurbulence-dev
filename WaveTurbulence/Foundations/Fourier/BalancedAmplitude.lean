/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BalancedPhase
public import WaveTurbulence.Foundations.Fourier.CoordinateCutoffDerivative
public import WaveTurbulence.Foundations.Fourier.DirectionalFourierMoments
import Mathlib.Tactic

/-!
# Uniform diagonal derivative bounds for the A.3 amplitudes

The balanced phase has modulus one and zero simultaneous-translation
derivative. Consequently neither amplitude bound contains its frequencies.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- A cutoff, balanced phase, and two-coordinate source amplitude. -/
@[expose] noncomputable def balancedCutoffAmplitude {n : ℕ} (χ : ℝ → ℝ)
    (a : Fin n → ℝ) (F : (Fin 2 → ℝ) → ℂ) (i j : Fin n) (v : Fin n → ℝ) : ℂ :=
  coordinateCutoff χ v * linearTimePhase a v * F ![v i, v j]

/-- Smoothness of the amplitude for arbitrary real phase coefficients. -/
theorem balancedCutoffAmplitude_contDiff {n : ℕ} {χ : ℝ → ℝ}
    {F : (Fin 2 → ℝ) → ℂ} (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F)
    (a : Fin n → ℝ) (i j : Fin n) : ContDiff ℝ ∞ (balancedCutoffAmplitude χ a F i j) := by
  apply ((coordinateCutoff_contDiff hχ).mul (linearTimePhase_contDiff a)).mul
  apply hF.comp
  apply contDiff_pi.mpr
  intro k
  fin_cases k
  · change ContDiff ℝ ∞ (fun v : Fin n → ℝ => v i)
    fun_prop
  · change ContDiff ℝ ∞ (fun v : Fin n → ℝ => v j)
    fun_prop

/-- The input amplitude is bounded without any dependence on the phase coefficients. -/
theorem norm_balancedCutoffAmplitude_le {n : ℕ} {χ : ℝ → ℝ} (h : CutoffControl χ)
    (a : Fin n → ℝ) (F : (Fin 2 → ℝ) → ℂ) (i j : Fin n) (v : Fin n → ℝ) :
    ‖balancedCutoffAmplitude χ a F i j v‖ ≤ h.bound ^ n * ‖F ![v i, v j]‖ := by
  unfold balancedCutoffAmplitude
  rw [norm_mul, norm_mul, norm_linearTimePhase, mul_one]
  exact mul_le_mul_of_nonneg_right (norm_coordinateCutoff_le h v) (norm_nonneg _)

/-- A balanced amplitude's diagonal derivative contains only cutoff and source derivatives. -/
theorem timeDirectionalDerivative_balancedCutoffAmplitude {n : ℕ} {χ : ℝ → ℝ}
    {F : (Fin 2 → ℝ) → ℂ} (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F)
    {a : Fin n → ℝ} (ha : ∑ k, a k = 0) (i j : Fin n) (v : Fin n → ℝ) :
    timeDirectionalDerivative (fun _ => 1) (balancedCutoffAmplitude χ a F i j) v =
      coordinateCutoffDiagonal χ v * linearTimePhase a v * F ![v i, v j] +
      coordinateCutoff χ v * linearTimePhase a v *
        (WaveTurbulence.partialDeriv 0 F ![v i, v j] + WaveTurbulence.partialDeriv 1 F ![v i, v j]) := by
  have hFc := hasDerivAt_diagonal_translation (hF.differentiable (by simp)) ![v i, v j]
  rw [timeDirectionalDerivative_diagonal_eq_partials (hF.differentiable (by simp))] at hFc
  have hFcurve : HasDerivAt (fun c : ℝ => F ![v i + c, v j + c])
      (WaveTurbulence.partialDeriv 0 F ![v i, v j] + WaveTurbulence.partialDeriv 1 F ![v i, v j]) 0 := by
    convert hFc using 1
    funext c
    congr 1
    ext k
    fin_cases k <;> rfl
  have hp := (((hasDerivAt_coordinateCutoff_diagonal hχ v).mul
    (hasDerivAt_linearTimePhase_diagonal ha v 0)).mul hFcurve)
  have hs := hasDerivAt_diagonal_translation
    ((balancedCutoffAmplitude_contDiff hχ hF a i j).differentiable (by simp)) v
  have he := hs.unique hp
  simpa only [balancedCutoffAmplitude, add_zero, Pi.mul_apply, mul_zero] using he

/-- Uniform diagonal amplitude bound, with the source first derivatives localized later. -/
theorem norm_diagonal_balancedCutoffAmplitude_le {n : ℕ} {χ : ℝ → ℝ}
    {F : (Fin 2 → ℝ) → ℂ} (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F)
    (h : CutoffControl χ) {a : Fin n → ℝ} (ha : ∑ k, a k = 0)
    (i j : Fin n) (v : Fin n → ℝ) :
    ‖timeDirectionalDerivative (fun _ => 1) (balancedCutoffAmplitude χ a F i j) v‖ ≤
      ((n : ℝ) * h.bound ^ (n + 1)) * ‖F ![v i, v j]‖ +
      h.bound ^ n * (‖WaveTurbulence.partialDeriv 0 F ![v i, v j]‖ +
        ‖WaveTurbulence.partialDeriv 1 F ![v i, v j]‖) := by
  rw [timeDirectionalDerivative_balancedCutoffAmplitude hχ hF ha]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul, norm_mul, norm_linearTimePhase, mul_one]
    exact mul_le_mul_of_nonneg_right (norm_coordinateCutoffDiagonal_le h v) (norm_nonneg _)
  · rw [norm_mul, norm_mul, norm_linearTimePhase, mul_one]
    exact mul_le_mul (norm_coordinateCutoff_le h v) (norm_add_le _ _)
      (norm_nonneg _) (pow_nonneg (by linarith [h.one_le_bound]) n)

end WaveTurbulence.Fourier
