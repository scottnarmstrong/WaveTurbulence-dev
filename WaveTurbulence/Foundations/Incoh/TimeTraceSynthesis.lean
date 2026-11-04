/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TimeCoordinateFreeze
public import WaveTurbulence.Foundations.Fourier.CoordinateCutoff
public import WaveTurbulence.Foundations.Fourier.TimeEuclidean
public import WaveTurbulence.Foundations.Fourier.TimeBasic

/-!
# Fourier synthesis of a fixed-clock trace

A compact output cutoff makes the synthesis jointly integrable. Fixing
one time contributes only a unit phase in its removed frequency.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- Freeze one clock and apply the fixed cutoff in every output coordinate. -/
@[expose] def cutoffTimeTrace {r : ℕ} (χ : ℝ → ℝ) (j : Fin r) (c : ℝ)
    (F : (Fin r → ℝ) → ℂ) (t : Fin r → ℝ) : ℂ :=
  Fourier.coordinateCutoff χ t * F (Function.update t j c)

/-- The synthesis kernel at the surviving output frequency. -/
@[expose] def frozenModulation {r : ℕ} (χ : ℝ → ℝ) (j : Fin r)
    (t ξ : Fin r → ℝ) : ℂ :=
  Real.fourierChar (Fourier.timePairing r t (eraseTimeFrequency j ξ)) • Fourier.coordinateCutoff χ t

/-- Exact pointwise inversion formula for a cutoff trace. -/
theorem cutoffTimeTrace_eq_fourier_mixture {r : ℕ} (χ : ℝ → ℝ) (j : Fin r) (c : ℝ)
    {F : (Fin r → ℝ) → ℂ} (hF : Integrable F) (hhF : Integrable (Fourier.timeFourier F))
    (hcF : Continuous F) (t : Fin r → ℝ) :
    cutoffTimeTrace χ j c F t = ∫ ξ,
      ((Real.fourierChar (c * ξ j) : ℂ) * Fourier.timeFourier F ξ) * frozenModulation χ j t ξ := by
  unfold cutoffTimeTrace
  rw [← Fourier.timeFourier_inversion hF hhF hcF (Function.update t j c)]
  change Fourier.coordinateCutoff χ t *
    (∫ ξ, Real.fourierChar (-Fourier.timePairing r ξ (-Function.update t j c)) •
      Fourier.timeFourier F ξ) = _
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    dsimp only
    have hn : -Fourier.timePairing r ξ (-Function.update t j c) =
        Fourier.timePairing r t (eraseTimeFrequency j ξ) + c * ξ j := by
      rw [map_neg, neg_neg, timePairing_update]
    rw [hn]
    rw [AddChar.map_add_eq_mul]
    simp only [frozenModulation, Circle.smul_def, smul_eq_mul, Circle.coe_mul]
    ring)

/-- The synthesis kernel has precisely the modulus of the fixed cutoff. -/
theorem norm_frozenModulation {r : ℕ} (χ : ℝ → ℝ) (j : Fin r) (t ξ : Fin r → ℝ) :
    ‖frozenModulation χ j t ξ‖ = ‖Fourier.coordinateCutoff χ t‖ := by
  exact Circle.norm_smul _ _

/-- Its scalar Fourier norm has the weight of the surviving frequency. -/
theorem timeFourierNorm_frozenModulation_le {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    (χ : ℝ → ℝ) (j : Fin r) (ξ : Fin r → ℝ) :
    Fourier.timeFourierNorm θ (fun t => frozenModulation χ j t ξ) ≤
      ENNReal.ofReal (2 ^ θ) * Fourier.timeWeight θ ξ *
        Fourier.timeFourierNorm θ (Fourier.coordinateCutoff (r := r) χ) :=
  (Fourier.timeFourierNorm_modulate_le hθ _ (eraseTimeFrequency j ξ)).trans
    (mul_le_mul' (mul_le_mul' le_rfl (timeWeight_eraseTimeFrequency_le hθ j ξ)) le_rfl)

end WaveTurbulence.Incoh
