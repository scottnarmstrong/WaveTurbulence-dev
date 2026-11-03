/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BalancedAmplitudeBox
public import WaveTurbulence.Foundations.Fourier.BoxMiddleCoordinates
public import WaveTurbulence.Foundations.Fourier.MixedDerivativeBoxBounds
import Mathlib.Tactic

/-!
# Uniform source bounds for the A.3 amplitude box integrals

The compact smooth source class is the owner's ruling for TARGET A.3.
Its mixed derivative controls the amplitude and local first derivatives
without any dependence on the support radius of the source function.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- Explicit amplitude factor for the twofold operator. -/
@[expose] noncomputable def triangularAmplitudeFactor (R C : ℝ) : ℝ≥0∞ :=
  (3 * ENNReal.ofReal (C ^ 2) + ENNReal.ofReal (2 * C ^ 3)) * volume (Icc (-R) R) ^ 2 +
    2 * ENNReal.ofReal (C ^ 2) * volume (Icc (-R) R)

/-- Explicit amplitude factor for the fourfold operator. -/
@[expose] noncomputable def fourfoldAmplitudeFactor (R C : ℝ) : ℝ≥0∞ :=
  (3 * ENNReal.ofReal (C ^ 4) + ENNReal.ofReal (4 * C ^ 5)) * volume (Icc (-R) R) ^ 4 +
    2 * ENNReal.ofReal (C ^ 4) * volume (Icc (-R) R) ^ 3

/-- The twofold amplitude and its diagonal derivative are controlled by the mixed derivative. -/
theorem triangular_amplitude_boxes_le {χ : ℝ → ℝ} {F : (Fin 2 → ℝ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (h : CutoffControl χ) (Γ : ℝ) :
    (3 * boxIntegral 2 (fun v => ‖balancedCutoffAmplitude χ ![Γ, -Γ] F 0 1 v‖ₑ) h.radius +
      boxIntegral 2 (fun v => ‖timeDirectionalDerivative (fun _ => 1)
        (balancedCutoffAmplitude χ ![Γ, -Γ] F 0 1) v‖ₑ) h.radius) ≤
      triangularAmplitudeFactor h.radius h.bound * ∫⁻ x, ‖mixedTimePartial F x‖ₑ := by
  have hbal : ∑ j, (![Γ, -Γ] : Fin 2 → ℝ) j = 0 := by simp [Fin.sum_univ_two]
  have hB := boxIntegral_balancedCutoffAmplitude_le h ![Γ, -Γ] F (0 : Fin 2) 1 h.radius
  have hD := boxIntegral_diagonal_balancedCutoffAmplitude_le hχ hF h hbal (0 : Fin 2) 1 h.radius
  rw [boxIntegral_two_coordinate_pair (fun v => ‖F v‖ₑ) h.radius] at hB
  rw [boxIntegral_two_coordinate_pair (fun v => ‖F v‖ₑ) h.radius,
    boxIntegral_two_coordinate_pair (fun v => ‖WaveTurbulence.partialDeriv 0 F v‖ₑ) h.radius,
    boxIntegral_two_coordinate_pair (fun v => ‖WaveTurbulence.partialDeriv 1 F v‖ₑ) h.radius] at hD
  have hBF := boxIntegral_amplitude_le_mixed hF hc h.radius
  have hB₀ := boxIntegral_partial_zero_le_mixed hF hc h.radius
  have hB₁ := boxIntegral_partial_one_le_mixed hF hc h.radius
  have hB' := hB.trans (mul_le_mul' le_rfl hBF)
  have hD' := hD.trans (add_le_add (mul_le_mul' le_rfl hBF)
    (mul_le_mul' le_rfl (add_le_add hB₀ hB₁)))
  exact (add_le_add (mul_le_mul' le_rfl hB') hD').trans_eq (by
    unfold triangularAmplitudeFactor
    ring_nf)

/-- The fourfold amplitude uses the middle source coordinates and the same mixed derivative norm. -/
theorem fourfold_amplitude_boxes_le {χ : ℝ → ℝ} {F : (Fin 2 → ℝ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (h : CutoffControl χ) (Γ₁ Γ₂ : ℝ) :
    (3 * boxIntegral 4 (fun v => ‖balancedCutoffAmplitude χ ![Γ₁, -Γ₁, Γ₂, -Γ₂] F 1 2 v‖ₑ) h.radius +
      boxIntegral 4 (fun v => ‖timeDirectionalDerivative (fun _ => 1)
        (balancedCutoffAmplitude χ ![Γ₁, -Γ₁, Γ₂, -Γ₂] F 1 2) v‖ₑ) h.radius) ≤
      fourfoldAmplitudeFactor h.radius h.bound * ∫⁻ x, ‖mixedTimePartial F x‖ₑ := by
  have hbal : ∑ j, (![Γ₁, -Γ₁, Γ₂, -Γ₂] : Fin 4 → ℝ) j = 0 := by simp [Fin.sum_univ_succ]
  have hB := boxIntegral_balancedCutoffAmplitude_le h ![Γ₁, -Γ₁, Γ₂, -Γ₂] F (1 : Fin 4) 2 h.radius
  have hD := boxIntegral_diagonal_balancedCutoffAmplitude_le hχ hF h hbal (1 : Fin 4) 2 h.radius
  rw [boxIntegral_four_middle (fun v => ‖F v‖ₑ) h.radius] at hB
  rw [boxIntegral_four_middle (fun v => ‖F v‖ₑ) h.radius,
    boxIntegral_four_middle (fun v => ‖WaveTurbulence.partialDeriv 0 F v‖ₑ) h.radius,
    boxIntegral_four_middle (fun v => ‖WaveTurbulence.partialDeriv 1 F v‖ₑ) h.radius] at hD
  let w := volume (Icc (-h.radius) h.radius)
  let M := ∫⁻ x, ‖mixedTimePartial F x‖ₑ
  have hBF : w ^ 2 * boxIntegral 2 (fun v => ‖F v‖ₑ) h.radius ≤ w ^ 4 * M :=
    (mul_le_mul' le_rfl (boxIntegral_amplitude_le_mixed hF hc h.radius)).trans_eq (by ring)
  have hB₀ : w ^ 2 * boxIntegral 2 (fun v => ‖WaveTurbulence.partialDeriv 0 F v‖ₑ) h.radius ≤ w ^ 3 * M :=
    (mul_le_mul' le_rfl (boxIntegral_partial_zero_le_mixed hF hc h.radius)).trans_eq (by ring)
  have hB₁ : w ^ 2 * boxIntegral 2 (fun v => ‖WaveTurbulence.partialDeriv 1 F v‖ₑ) h.radius ≤ w ^ 3 * M :=
    (mul_le_mul' le_rfl (boxIntegral_partial_one_le_mixed hF hc h.radius)).trans_eq (by ring)
  have hB' := hB.trans (mul_le_mul' le_rfl hBF)
  have hD' := hD.trans (add_le_add (mul_le_mul' le_rfl hBF)
    (mul_le_mul' le_rfl (add_le_add hB₀ hB₁)))
  exact (add_le_add (mul_le_mul' le_rfl hB') hD').trans_eq (by
    unfold fourfoldAmplitudeFactor
    dsimp [w, M]
    ring_nf)

/-- Both explicit amplitude factors are finite. -/
theorem phaseAmplitudeFactors_ne_top (R C : ℝ) :
    triangularAmplitudeFactor R C ≠ ⊤ ∧ fourfoldAmplitudeFactor R C ≠ ⊤ := by
  have hw : volume (Icc (-R) R) < ⊤ := isCompact_Icc.measure_lt_top
  constructor
  · unfold triangularAmplitudeFactor
    finiteness
  · unfold fourfoldAmplitudeFactor
    finiteness

end WaveTurbulence.Fourier
