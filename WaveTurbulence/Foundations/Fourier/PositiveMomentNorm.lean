/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourierEndpointSum
public import WaveTurbulence.Foundations.Fourier.FourierWeightedHolder
public import WaveTurbulence.Foundations.Fourier.RectangleFourLpMoments
import Mathlib.Tactic

/-!
# Positive time Fourier norms from four Lp endpoint moments

This is the physical-derivative repair of TARGET A.2's logarithm-defective
convolution step. Hausdorff–Young has constant one throughout.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- Compact support is preserved by each square-free endpoint derivative. -/
theorem fourTimeDerivatives_hasCompactSupport {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (j : Fin 4) : HasCompactSupport (fourTimeDerivatives f j) := by
  fin_cases j
  · exact hc
  · exact hasCompactSupport_partialDeriv (hf.differentiable (by simp)) hc 0
  · exact hasCompactSupport_partialDeriv (hf.differentiable (by simp)) hc 1
  · exact hasCompactSupport_partialDeriv
      ((WaveTurbulence.contDiff_infty_partialDeriv hf 1).differentiable (by simp))
      (hasCompactSupport_partialDeriv (hf.differentiable (by simp)) hc 1) 0

/-- Pointwise positive-weight control, retaining the actual derivative transforms. -/
theorem timeWeight_mul_enorm_fourier_le_endpoint_sum {η : ℝ} (hη : 0 ≤ η)
    {f : (Fin 2 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (ξ : Fin 2 → ℝ) :
    timeWeight η ξ * ‖timeFourier f ξ‖ₑ ≤
      4 * ENNReal.ofReal (positiveFrequencyEnvelope η ξ) *
        ∑ j : Fin 4, ‖timeFourier (fourTimeDerivatives f j) ξ‖ₑ := by
  let S := ∑ j : Fin 4, ‖timeFourier (fourTimeDerivatives f j) ξ‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hw := Real.rpow_nonneg (timeBracket_pos ξ).le η
  have hr : timeBracket ξ ^ η * ‖timeFourier f ξ‖ ≤
      4 * positiveFrequencyEnvelope η ξ * S := by
    calc
      _ ≤ timeBracket ξ ^ η * (4 * S /
        (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2))) :=
        mul_le_mul_of_nonneg_left (norm_timeFourier_le_two_brackets_fourier_sum hf hc ξ) hw
      _ = (4 * S) * (timeBracket ξ ^ η /
        (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2))) := by ring
      _ ≤ (4 * S) * positiveFrequencyEnvelope η ξ :=
        mul_le_mul_of_nonneg_left (positive_weight_two_brackets_le hη ξ) (by positivity)
      _ = _ := by ring
  change ENNReal.ofReal (timeBracket ξ ^ η) * ‖timeFourier f ξ‖ₑ ≤ _
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hw]
  apply (ENNReal.ofReal_le_ofReal hr).trans_eq
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) (positiveFrequencyEnvelope_nonneg η ξ)),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  simp only [ofReal_norm]

/-- Positive Fourier regularity is controlled by the four endpoint `Lᵖ` norms. -/
theorem timeFourierNorm_positive_le_four_Lp {η p q : ℝ} (hη : 0 ≤ η)
    (hpq : p.HolderConjugate q) (hp2 : p ≤ 2)
    {f : (Fin 2 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    timeFourierNorm η f ≤ (4 * positiveFrequencyFactor η p) *
      fourTimeLpNorm (ENNReal.ofReal p) f := by
  have hi (j : Fin 4) : Integrable (fourTimeDerivatives f j) :=
    (fourTimeDerivatives_contDiff hf j).continuous.integrable_of_hasCompactSupport
      (fourTimeDerivatives_hasCompactSupport hf hc j)
  have hm (j : Fin 4) : Measurable (fun ξ =>
      ENNReal.ofReal (positiveFrequencyEnvelope η ξ) *
        ‖timeFourier (fourTimeDerivatives f j) ξ‖ₑ) := by
    apply Measurable.mul _ (timeFourier_continuous (hi j)).measurable.enorm
    unfold positiveFrequencyEnvelope inverseBracketPower
    fun_prop
  rw [timeFourierNorm_eq_lintegral (hf.continuous.integrable_of_hasCompactSupport hc)]
  calc
    _ ≤ ∫⁻ ξ, 4 * ENNReal.ofReal (positiveFrequencyEnvelope η ξ) *
        ∑ j : Fin 4, ‖timeFourier (fourTimeDerivatives f j) ξ‖ₑ :=
      lintegral_mono (timeWeight_mul_enorm_fourier_le_endpoint_sum hη hf hc)
    _ = 4 * ∑ j : Fin 4, ∫⁻ ξ, ENNReal.ofReal (positiveFrequencyEnvelope η ξ) *
        ‖timeFourier (fourTimeDerivatives f j) ξ‖ₑ := by
      simp_rw [mul_assoc]
      rw [lintegral_const_mul' _ _ (by norm_num)]
      congr 1
      simp_rw [Finset.mul_sum]
      exact lintegral_finsetSum _ (fun j _ => hm j)
    _ ≤ 4 * ∑ j : Fin 4, positiveFrequencyFactor η p *
        eLpNorm (fourTimeDerivatives f j) (ENNReal.ofReal p) := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro j _
      exact lintegral_positiveEnvelope_fourier_le hpq hp2 (hi j)
        ((fourTimeDerivatives_contDiff hf j).continuous.memLp_of_hasCompactSupport
          (fourTimeDerivatives_hasCompactSupport hf hc j))
    _ = _ := by rw [← Finset.mul_sum]; unfold fourTimeLpNorm; ring

end WaveTurbulence.Fourier
