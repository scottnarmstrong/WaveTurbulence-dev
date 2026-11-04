/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Norm00V
public import WaveTurbulence.Foundations.Fourier.TimeFourier

/-! # Common time translations of parameter-family Fourier norms -/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- A common external time translation preserves the full parameter supremum Fourier norm. -/
theorem mixedFourierNorm00_translate_of_integrable {r : ℕ} {V : Type*} (θ : ℝ)
    (F : (Fin r → ℝ) → V → ℂ) (a : Fin r → ℝ)
    (hF : ∀ v, Integrable (fun t => F t v)) :
    Fourier.mixedFourierNorm00 θ (fun t v => F (t + a) v) = Fourier.mixedFourierNorm00 θ F := by
  rw [Fourier.mixedFourierNorm00_eq_lintegral (fun v => (hF v).comp_add_right a),
    Fourier.mixedFourierNorm00_eq_lintegral hF]
  apply lintegral_congr
  intro ξ
  congr 1
  unfold Fourier.mixedFourierEnvelope00
  apply iSup_congr
  intro v
  dsimp only
  rw [Fourier.timeFourier_translate (fun t => F t v) a]
  simp only [Circle.enorm_smul]

end WaveTurbulence.Incoh
