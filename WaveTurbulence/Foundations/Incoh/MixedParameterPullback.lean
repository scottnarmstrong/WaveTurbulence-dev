/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Norm00V

/-!
# Pulling back arbitrary parameters in the mixed Fourier norm

No measurability of the parameter map is needed: the parameter supremum
is inside the Fourier integral and no parameter measure is involved.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Restricting a family along any parameter map decreases its mixed norm. -/
theorem mixedFourierNorm00_comp_le {r : ℕ} {V W : Type*} (θ : ℝ)
    (F : (Fin r → ℝ) → W → ℂ) (p : V → W) :
    Fourier.mixedFourierNorm00 θ (fun t v => F t (p v)) ≤ Fourier.mixedFourierNorm00 θ F := by
  by_cases hF : ∀ w, Integrable (fun t => F t w)
  · rw [Fourier.mixedFourierNorm00_eq_lintegral (fun v => hF (p v)),
      Fourier.mixedFourierNorm00_eq_lintegral hF]
    apply lintegral_mono
    intro ξ
    apply mul_le_mul' le_rfl
    apply iSup_le
    intro v
    exact le_iSup (fun w => ‖Fourier.timeFourier (fun t => F t w) ξ‖ₑ) (p v)
  · rw [Fourier.mixedFourierNorm00_of_not_integrable hF]
    exact le_top

end WaveTurbulence.Incoh
