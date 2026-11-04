/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.ThreeMomentNorm
public import WaveTurbulence.Foundations.Fourier.Norm00V

/-!
# The landed three-moment bound with arbitrary vector parameters

The scalar frequency estimate and its integrable envelope are reused
verbatim. Only the parameter carrier is generalized; no parameter measure
or regularity is involved at order zero.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- A common scalar moment bound controls the mixed norm on any parameter carrier. -/
theorem mixedFourierNorm00_le_threeMoment_bound {V : Type*}
    {F : (Fin 2 → ℝ) → V → ℂ} (hF : ∀ v, ContDiff ℝ ∞ (fun t => F t v))
    (hc : ∀ v, HasCompactSupport (fun t => F t v)) {M : ℝ≥0∞}
    (hM : ∀ v, ENNReal.ofReal (Fourier.threeTimeMomentSum (fun t => F t v)) ≤ M) :
    Fourier.mixedFourierNorm00 (1 / 4) F ≤ ENNReal.ofReal (8 * Fourier.jointFrequencyConstant) * M := by
  let B := fun ξ : Fin 2 → ℝ => ENNReal.ofReal (8 * Fourier.jointFrequencyEnvelope (ξ 0, ξ 1))
  have hB : Measurable B :=
    (measurable_const.mul (Fourier.jointFrequencyEnvelope_measurable.comp (by fun_prop))).ennreal_ofReal
  have hi (v : V) : Integrable (fun t => F t v) := (hF v).continuous.integrable_of_hasCompactSupport (hc v)
  have hp (ξ : Fin 2 → ℝ) : Fourier.timeWeight (1 / 4) ξ * Fourier.mixedFourierEnvelope00 F ξ ≤ B ξ * M := by
    unfold Fourier.mixedFourierEnvelope00
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro v
    exact (Fourier.timeWeight_mul_enorm_timeFourier_le_three_moments (hF v) (hc v) ξ).trans
      (mul_le_mul' le_rfl (hM v))
  have hInt : (∫⁻ ξ, B ξ) ≤ ENNReal.ofReal (8 * Fourier.jointFrequencyConstant) := by
    have hiB := Fourier.jointFrequencyEnvelope_coordinates_integrable.const_mul (8 : ℝ)
    have hn : 0 ≤ᵐ[volume] (fun ξ : Fin 2 → ℝ => 8 * Fourier.jointFrequencyEnvelope (ξ 0, ξ 1)) :=
      Filter.Eventually.of_forall (fun _ => mul_nonneg (by norm_num) (Fourier.jointFrequencyEnvelope_nonneg _))
    rw [show (∫⁻ ξ, B ξ) = ENNReal.ofReal (∫ ξ : Fin 2 → ℝ,
      8 * Fourier.jointFrequencyEnvelope (ξ 0, ξ 1)) from (ofReal_integral_eq_lintegral_ofReal hiB hn).symm]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_const_mul]
    dsimp only [Fourier.jointFrequencyConstant]
    linarith
  rw [Fourier.mixedFourierNorm00_eq_lintegral hi]
  exact (lintegral_mono hp).trans ((lintegral_mul_const M hB).le.trans (mul_le_mul' hInt le_rfl))

end WaveTurbulence.Incoh
