/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeInterpolation
import Mathlib.Tactic

/-!
# Basic operations on time Fourier norms

Triangle inequality, scalar multiplication, and modulation for TARGET
`(normX1)`, with the extended-value convention at nonintegrable inputs.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

private theorem timePairing_continuous (r : ℕ) :
    Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => timePairing r p.1 p.2) := by
  change Continuous (fun p : (Fin r → ℝ) × (Fin r → ℝ) => ∑ j, p.1 j * p.2 j)
  fun_prop

theorem timeFourier_add {r : ℕ} {f g : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    timeFourier (fun t => f t + g t) = fun ξ => timeFourier f ξ + timeFourier g ξ :=
  VectorFourier.fourierIntegral_add Real.continuous_fourierChar (timePairing_continuous r) hf hg

theorem timeFourierNorm_add_le {r : ℕ} (θ : ℝ) (f g : (Fin r → ℝ) → ℂ) :
    timeFourierNorm θ (fun t => f t + g t) ≤ timeFourierNorm θ f + timeFourierNorm θ g := by
  classical
  by_cases hf : Integrable f
  · by_cases hg : Integrable g
    · have hfg : Integrable (fun t => f t + g t) := hf.add hg
      rw [timeFourierNorm_eq_lintegral hfg, timeFourierNorm_eq_lintegral hf,
        timeFourierNorm_eq_lintegral hg, timeFourier_add hf hg]
      calc
        _ ≤ ∫⁻ ξ, timeWeight θ ξ * ‖timeFourier f ξ‖ₑ +
            timeWeight θ ξ * ‖timeFourier g ξ‖ₑ := by
          apply lintegral_mono
          intro ξ
          dsimp only
          rw [← mul_add]
          exact mul_le_mul_right (enorm_add_le _ _) _
        _ = _ := lintegral_add_left
          ((timeWeight_measurable θ).mul (timeFourier_continuous hf).measurable.enorm) _
    · simp [timeFourierNorm_of_not_integrable hg]
  · simp [timeFourierNorm_of_not_integrable hf]

/-- Fourier transform of a complex scalar multiple. -/
theorem timeFourier_smul {r : ℕ} (c : ℂ) (f : (Fin r → ℝ) → ℂ) :
    timeFourier (fun t => c • f t) = fun ξ => c • timeFourier f ξ :=
  VectorFourier.fourierIntegral_const_smul _ _ _ _ _

/-- Exact homogeneity, including the zero scalar and infinite norm cases. -/
theorem timeFourierNorm_smul {r : ℕ} (θ : ℝ) (c : ℂ) (f : (Fin r → ℝ) → ℂ) :
    timeFourierNorm θ (fun t => c • f t) = ‖c‖ₑ * timeFourierNorm θ f := by
  classical
  by_cases hc : c = 0
  · subst c
    simp
  have hi : Integrable (fun t => c • f t) ↔ Integrable f := integrable_smul_iff hc f
  unfold timeFourierNorm
  rw [hi]
  split_ifs with hf
  · rw [timeFourier_smul]
    simp only [enorm_smul, mul_left_comm (timeWeight θ _) ‖c‖ₑ]
    exact lintegral_const_mul _ ((timeWeight_measurable θ).mul
      (timeFourier_continuous hf).measurable.enorm)
  · simp [hc]

/-- Modulation by the positive Fourier character translates frequencies. -/
theorem timeFourier_modulate {r : ℕ} (f : (Fin r → ℝ) → ℂ) (a : Fin r → ℝ) :
    timeFourier (fun t => Real.fourierChar (timePairing r t a) • f t) =
      fun ξ => timeFourier f (ξ - a) := by
  funext ξ
  unfold timeFourier VectorFourier.fourierIntegral
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only
    rw [← mul_smul, ← AddChar.map_add_eq_mul]
    have he : -timePairing r t ξ + timePairing r t a = -timePairing r t (ξ - a) := by
      rw [map_sub]
      ring
    rw [he]

/-- Modulation changes a nonnegative weighted Fourier norm by at most the
frequency weight of the modulation, up to the factor `2^θ`. -/
theorem timeFourierNorm_modulate_le {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    (f : (Fin r → ℝ) → ℂ) (a : Fin r → ℝ) :
    timeFourierNorm θ (fun t => Real.fourierChar (timePairing r t a) • f t) ≤
      ENNReal.ofReal (2 ^ θ) * timeWeight θ a * timeFourierNorm θ f := by
  classical
  have hi : Integrable (fun t => Real.fourierChar (timePairing r t a) • f t) ↔
      Integrable f := by
    simpa only [map_neg, neg_neg] using VectorFourier.fourierIntegral_convergent_iff
      Real.continuous_fourierChar (timePairing_continuous r) (-a) (f := f) (μ := volume)
  have hK : ENNReal.ofReal (2 ^ θ) * timeWeight θ a ≠ 0 := by
    apply mul_ne_zero
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (timeBracket_pos a) _))
  unfold timeFourierNorm
  rw [hi]
  split_ifs with hf
  · rw [timeFourier_modulate]
    have hs := lintegral_add_right_eq_self (μ := (volume : Measure (Fin r → ℝ)))
      (fun ξ => timeWeight θ ξ * ‖timeFourier f (ξ - a)‖ₑ) a
    rw [← hs]
    simp only [add_sub_cancel_right]
    calc
      _ ≤ ∫⁻ ξ, (ENNReal.ofReal (2 ^ θ) * timeWeight θ a) *
          (timeWeight θ ξ * ‖timeFourier f ξ‖ₑ) := by
        apply lintegral_mono
        intro ξ
        have h := mul_le_mul_left (timeWeight_add_le hθ ξ a) ‖timeFourier f ξ‖ₑ
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := lintegral_const_mul _ ((timeWeight_measurable θ).mul
        (timeFourier_continuous hf).measurable.enorm)
  · simp only [ENNReal.mul_top hK, le_refl]

end WaveTurbulence.Fourier
