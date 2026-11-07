/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.NormModulation

/-!
# Integrating a uniform Fourier majorant without exchanging the output supremum

This elementary estimate keeps the general output carrier and the exact
integrability guard. It is used for the negative endpoint of the local
extension, where all output dependence has a common scalar majorant.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- An integrable scalar majorant for the weighted Fourier envelopes bounds
the exact norm, with the supremum retained inside its integral. -/
theorem mixedFourierNorm00_le_integral_majorant {r : ℕ} {V : Type*}
    (s : ℝ) (F : (Fin r → ℝ) → V → ℂ) (hF : ∀ v, Integrable (fun t => F t v))
    (g : (Fin r → ℝ) → ℝ) (hg : Integrable g) (hgn : ∀ ξ, 0 ≤ g ξ)
    (hb : ∀ ξ v, (Fourier.timeBracket ξ)^s *
      ‖Fourier.timeFourier (fun t => F t v) ξ‖ ≤ g ξ) :
    Fourier.mixedFourierNorm00 s F ≤ ENNReal.ofReal (∫ ξ, g ξ) := by
  rw [Fourier.mixedFourierNorm00_eq_lintegral hF,
    ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hgn)]
  apply lintegral_mono
  intro ξ
  change ENNReal.ofReal ((Fourier.timeBracket ξ)^s) *
    (⨆ v, ‖Fourier.timeFourier (fun t => F t v) ξ‖ₑ) ≤ ENNReal.ofReal (g ξ)
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro v
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.rpow_nonneg (Fourier.timeBracket_pos ξ).le _)]
  exact ENNReal.ofReal_le_ofReal (hb ξ v)

end WaveTurbulence.SumintPar
