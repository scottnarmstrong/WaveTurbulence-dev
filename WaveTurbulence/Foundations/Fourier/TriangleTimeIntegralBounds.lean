/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.NegativeMomentNorm
public import WaveTurbulence.Foundations.Fourier.WeightedFourMoments
public import WaveTurbulence.Foundations.Fourier.CoordinateCutoffDerivative
public import WaveTurbulence.Foundations.Fourier.TimeOperatorRegularity
public import WaveTurbulence.Foundations.Fourier.BoxIntegralAlgebra
import Mathlib.Tactic

/-!
# TARGET A.2: the triangular bound on smooth time slices

This first form uses smooth input slices; their support is unrestricted.
Only the cutoff and the positive negative-regularity parameter enter the constant.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- Four endpoint moments of the triangle charge only the input `L¹` norm. -/
theorem fourTimeMomentNorm_triangle_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) {F : (Fin 2 → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) :
    fourTimeMomentNorm (cutoffTriangleIntegral χ F) ≤
      (orderedFourMomentFactor h.radius h.bound * ENNReal.ofReal (h.bound ^ 2)) *
        eLpNorm F 1 := by
  have hC : 0 ≤ h.bound := le_trans (by norm_num) h.one_le_bound
  rw [cutoffTriangleIntegral_eq_ordered, ← weightedOrderedIntegral_self]
  have hm := fourTimeMomentNorm_weighted_le (n := 0) hC hχ hχ
    (triangleAmplitude_contDiff hχ hF) h.endpointBounds h.deriv_endpointBounds
    h.endpointBounds h.deriv_endpointBounds
  apply hm.trans
  have hb : boxIntegral 2 (fun v => ‖triangleAmplitude χ F v‖ₑ) h.radius ≤
      ENNReal.ofReal (h.bound ^ 2) * eLpNorm F 1 := by
    calc
      _ ≤ boxIntegral 2 (fun v => ENNReal.ofReal (h.bound ^ 2) * ‖F v‖ₑ) h.radius := by
        apply boxIntegral_mono
        intro v
        rw [triangleAmplitude, enorm_mul]
        apply mul_le_mul_left
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_coordinateCutoff_le h v)
      _ = ENNReal.ofReal (h.bound ^ 2) * boxIntegral 2 (fun v => ‖F v‖ₑ) h.radius :=
        boxIntegral_const_mul 2 _ ENNReal.ofReal_ne_top _ _
      _ ≤ ENNReal.ofReal (h.bound ^ 2) * (∫⁻ v, ‖F v‖ₑ) :=
        mul_le_mul_right (boxIntegral_two_le_lintegral hF.continuous.measurable.enorm _) _
      _ ≤ _ := mul_le_mul_right lintegral_enorm_le_eLpNorm_one _
  exact (mul_le_mul_right hb _).trans_eq (by ring)

/-- TARGET A.2's triangular bound for arbitrary smooth time slices and arbitrary momentum dependence. -/
theorem mixedFourierNorm_cutoffJ_smooth_le {η : ℝ} (hη : 0 < η) {d : ℕ}
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (h : CutoffControl χ) {F : (Fin 2 → ℝ) → Mom d → ℂ}
    (hF : ∀ k, ContDiff ℝ ∞ (fun t => F t k)) :
    mixedFourierNorm (-η) 0 0 (cutoffJ χ F) ≤
      (ENNReal.ofReal (4 * negativeFrequencyConstant η) *
        orderedFourMomentFactor h.radius h.bound * ENNReal.ofReal (h.bound ^ 2)) *
          uniformTimeL1 F := by
  have hb := mixedFourierNorm_negative_le_four_moments hη
    (fun k => cutoffTriangleIntegral_contDiff hχ (hF k))
    (fun k => cutoffTriangleIntegral_hasCompactSupport hcχ (fun t => F t k))
  apply hb.trans
  have hs : (⨆ k, fourTimeMomentNorm (fun t => cutoffJ χ F t k)) ≤
      (orderedFourMomentFactor h.radius h.bound * ENNReal.ofReal (h.bound ^ 2)) *
        uniformTimeL1 F := by
    apply iSup_le
    intro k
    exact (fourTimeMomentNorm_triangle_le hχ h (hF k)).trans
      (mul_le_mul_right (le_iSup (fun k => eLpNorm (fun t => F t k) 1) k) _)
  exact (mul_le_mul_right hs _).trans_eq (by ring)

end WaveTurbulence.Fourier
