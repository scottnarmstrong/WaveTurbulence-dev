/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.MixedNorm
public import WaveTurbulence.Foundations.Fourier.TimeWeights
import Mathlib.Tactic

/-!
# Uniform Fourier majorants in the order-zero mixed norm

The momentum supremum stays inside the frequency integral. These analytic
helpers close operator estimates once their uniform Fourier decay is proved.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- An order-zero momentum norm is the literal pointwise supremum. -/
@[simp] theorem momentumSupNorm_zero {d : ℕ} (f : Mom d → ℂ) :
    momentumSupNorm 0 f = ⨆ k, ‖f k‖ₑ := by
  simp [momentumSupNorm]

/-- A majorant that already includes the time-frequency weight closes the mixed norm. -/
theorem mixedFourierNorm_zero_le_weighted_majorant {r d : ℕ}
    (θ : ℝ) {F : (Fin r → ℝ) → Mom d → ℂ}
    (hF : ∀ k, Integrable (fun t => F t k))
    {B : (Fin r → ℝ) → ℝ≥0∞} (hB : Measurable B) (M : ℝ≥0∞)
    (hb : ∀ ξ k, timeWeight θ ξ * ‖mixedTimeFourier F ξ k‖ₑ ≤ B ξ * M) :
    mixedFourierNorm θ 0 0 F ≤ (∫⁻ ξ, B ξ) * M := by
  rw [mixedFourierNorm_zero_order θ 0 F hF]
  calc
    _ ≤ ∫⁻ ξ, B ξ * M := by
      apply lintegral_mono
      intro ξ
      change timeWeight θ ξ * momentumSupNorm 0 (mixedTimeFourier F ξ) ≤ B ξ * M
      rw [momentumSupNorm_zero, ENNReal.mul_iSup]
      exact iSup_le (hb ξ)
    _ = _ := lintegral_mul_const M hB

end WaveTurbulence.Fourier
