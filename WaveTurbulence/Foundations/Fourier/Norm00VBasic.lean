/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.Norm00V
public import WaveTurbulence.Foundations.Fourier.TimeBasic

/-!
# Elementary bounds for the general-variable mixed Fourier norm

TARGET L581, L589. Triangle inequality and monotonicity retain both the
pointwise vector supremum and the time-integrability guard.
-/

public section

namespace WaveTurbulence.Fourier
open MeasureTheory
open scoped ENNReal

/-- Increasing time regularity increases the norm, including inadmissible inputs. -/
theorem mixedFourierNorm00_mono {r : ℕ} {V : Type*} {θ θ' : ℝ} (hθ : θ ≤ θ')
    (F : (Fin r → ℝ) → V → ℂ) : mixedFourierNorm00 θ F ≤ mixedFourierNorm00 θ' F := by
  by_cases hF : ∀ v, Integrable (fun t => F t v)
  · rw [mixedFourierNorm00_eq_lintegral hF, mixedFourierNorm00_eq_lintegral hF]
    exact lintegral_mono (fun ξ => mul_le_mul_left (timeWeight_mono hθ ξ) _)
  · rw [mixedFourierNorm00_of_not_integrable hF, mixedFourierNorm00_of_not_integrable hF]

/-- Triangle inequality for the vector Fourier envelopes. -/
theorem mixedFourierEnvelope00_add_le {r : ℕ} {V : Type*}
    {F G : (Fin r → ℝ) → V → ℂ}
    (hF : ∀ v, Integrable (fun t => F t v)) (hG : ∀ v, Integrable (fun t => G t v))
    (ξ : Fin r → ℝ) :
    mixedFourierEnvelope00 (fun t v => F t v + G t v) ξ ≤
      mixedFourierEnvelope00 F ξ + mixedFourierEnvelope00 G ξ := by
  apply iSup_le
  intro v
  rw [timeFourier_add (hF v) (hG v)]
  exact (enorm_add_le _ _).trans (add_le_add
    (le_iSup (fun v : V => ‖timeFourier (fun t => F t v) ξ‖ₑ) v)
    (le_iSup (fun v : V => ‖timeFourier (fun t => G t v) ξ‖ₑ) v))

/-- Triangle inequality for all inputs; a failed integrability guard gives infinity. -/
theorem mixedFourierNorm00_add_le {r : ℕ} {V : Type*} (θ : ℝ)
    (F G : (Fin r → ℝ) → V → ℂ) :
    mixedFourierNorm00 θ (fun t v => F t v + G t v) ≤
      mixedFourierNorm00 θ F + mixedFourierNorm00 θ G := by
  by_cases hF : ∀ v, Integrable (fun t => F t v)
  · by_cases hG : ∀ v, Integrable (fun t => G t v)
    · have hFG : ∀ v, Integrable (fun t => F t v + G t v) := fun v => (hF v).add (hG v)
      rw [mixedFourierNorm00_eq_lintegral hFG,
        mixedFourierNorm00_eq_lintegral hF, mixedFourierNorm00_eq_lintegral hG]
      calc
        _ ≤ ∫⁻ ξ, timeWeight θ ξ * (mixedFourierEnvelope00 F ξ + mixedFourierEnvelope00 G ξ) :=
          lintegral_mono (fun ξ => mul_le_mul_right (mixedFourierEnvelope00_add_le hF hG ξ) _)
        _ = _ := by
          simp_rw [mul_add]
          exact lintegral_add_left ((timeWeight_measurable θ).mul (measurable_mixedFourierEnvelope00 hF)) _
    · rw [mixedFourierNorm00_of_not_integrable hG, add_top]
      exact le_top
  · rw [mixedFourierNorm00_of_not_integrable hF, top_add]
    exact le_top

end WaveTurbulence.Fourier
