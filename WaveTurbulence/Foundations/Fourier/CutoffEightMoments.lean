/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.WeightedFourMoments
public import WaveTurbulence.Foundations.Fourier.WeightedDiagonalDerivative
import Mathlib.Tactic

/-!
# Eight actual time moments of a cutoff ordered operator

The diagonal product rule gives three weighted operators. Applying the
four-moment estimate to each one uses cutoff derivatives only through
order two and differentiates the amplitude only in the diagonal direction.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- The eight actual moments are bounded by the amplitude and its diagonal derivative on the cutoff box. -/
theorem threeTimeMomentSum_weighted_cutoff_le {n : ℕ} {χ : ℝ → ℝ}
    {A : (Fin (n + 2) → ℝ) → ℂ} (hχ : ContDiff ℝ ∞ χ) (hA : ContDiff ℝ ∞ A)
    (h : CutoffControl χ) :
    ENNReal.ofReal (threeTimeMomentSum (weightedOrderedIntegral (n + 2) χ χ A)) ≤
      orderedFourMomentFactor h.radius h.bound *
        (3 * boxIntegral (n + 2) (fun v => ‖A v‖ₑ) h.radius +
          boxIntegral (n + 2) (fun v => ‖timeDirectionalDerivative (fun _ => 1) A v‖ₑ) h.radius) := by
  let DA := timeDirectionalDerivative (fun _ => 1) A
  let T₀ := weightedOrderedIntegral (n + 2) (deriv χ) χ A
  let T₁ := weightedOrderedIntegral (n + 2) χ (deriv χ) A
  let T₂ := weightedOrderedIntegral (n + 2) χ χ DA
  have hχ' : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hDA : ContDiff ℝ ∞ DA := timeDirectionalDerivative_contDiff hA _
  have hT₀ : ContDiff ℝ ∞ T₀ := weightedOrderedIntegral_contDiff hχ' hχ hA
  have hT₁ : ContDiff ℝ ∞ T₁ := weightedOrderedIntegral_contDiff hχ hχ' hA
  have hT₂ : ContDiff ℝ ∞ T₂ := weightedOrderedIntegral_contDiff hχ hχ hDA
  have hC : 0 ≤ h.bound := le_trans zero_le_one h.one_le_bound
  have he : timeDirectionalDerivative (fun _ => 1) (weightedOrderedIntegral (n + 2) χ χ A) =
      fun t => T₀ t + T₁ t + T₂ t := by
    funext t
    exact timeDirectionalDerivative_weightedOrderedIntegral hχ hχ hA t
  have h₀ : fourTimeMomentNorm T₀ ≤ orderedFourMomentFactor h.radius h.bound *
      boxIntegral (n + 2) (fun v => ‖A v‖ₑ) h.radius :=
    fourTimeMomentNorm_weighted_le hC hχ' hχ hA h.deriv_endpointBounds
      h.second_deriv_endpointBounds h.endpointBounds h.deriv_endpointBounds
  have h₁ : fourTimeMomentNorm T₁ ≤ orderedFourMomentFactor h.radius h.bound *
      boxIntegral (n + 2) (fun v => ‖A v‖ₑ) h.radius :=
    fourTimeMomentNorm_weighted_le hC hχ hχ' hA h.endpointBounds
      h.deriv_endpointBounds h.deriv_endpointBounds h.second_deriv_endpointBounds
  have h₂ : fourTimeMomentNorm T₂ ≤ orderedFourMomentFactor h.radius h.bound *
      boxIntegral (n + 2) (fun v => ‖DA v‖ₑ) h.radius :=
    fourTimeMomentNorm_weighted_le hC hχ hχ hDA h.endpointBounds
      h.deriv_endpointBounds h.endpointBounds h.deriv_endpointBounds
  have hD : fourTimeMomentNorm (timeDirectionalDerivative (fun _ => 1)
      (weightedOrderedIntegral (n + 2) χ χ A)) ≤
      orderedFourMomentFactor h.radius h.bound *
        (2 * boxIntegral (n + 2) (fun v => ‖A v‖ₑ) h.radius +
          boxIntegral (n + 2) (fun v => ‖DA v‖ₑ) h.radius) := by
    rw [he]
    have hsum : ContDiff ℝ ∞ (fun t => T₀ t + T₁ t) := by convert hT₀.add hT₁ using 1
    apply (fourTimeMomentNorm_add_le hsum hT₂).trans
    apply (add_le_add (fourTimeMomentNorm_add_le hT₀ hT₁) le_rfl).trans
    exact (add_le_add (add_le_add h₀ h₁) h₂).trans_eq (by ring)
  have hf := weightedOrderedIntegral_contDiff hχ hχ hA
  have hc := weightedOrderedIntegral_hasCompactSupport h.endpointBounds h.endpointBounds A
  rw [ofReal_threeTimeMomentSum_eq_four hf hc]
  have hbase := fourTimeMomentNorm_weighted_le hC hχ hχ hA h.endpointBounds
    h.deriv_endpointBounds h.endpointBounds h.deriv_endpointBounds
  exact (add_le_add hbase hD).trans_eq (by ring)

end WaveTurbulence.Fourier
