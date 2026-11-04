/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.NormModulation

/-!
# Bounded multipliers depending only on the output

The external affine Fourier phase is such a multiplier. The estimate
retains the output supremum inside the frequency integral.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- An output multiplier of norm at most one costs no Fourier norm. -/
theorem mixedFourierNorm00_output_mul_le {r : ℕ} {V : Type*}
    (s : ℝ) (F : (Fin r → ℝ) → V → ℂ) (c : V → ℂ)
    (hc : ∀ v, ‖c v‖ₑ ≤ 1) :
    Fourier.mixedFourierNorm00 s (fun t v => c v * F t v) ≤
      Fourier.mixedFourierNorm00 s F := by
  by_cases hF : ∀ v, Integrable (fun t => F t v)
  · have hG : ∀ v, Integrable (fun t => c v * F t v) :=
      fun v => (hF v).const_mul _
    rw [Fourier.mixedFourierNorm00_eq_lintegral hG,
      Fourier.mixedFourierNorm00_eq_lintegral hF]
    apply lintegral_mono
    intro ξ
    apply mul_le_mul_right
    apply iSup_le
    intro v
    have he : Fourier.timeFourier (fun t => c v * F t v) ξ =
        c v * Fourier.timeFourier (fun t => F t v) ξ :=
      congrFun (Fourier.timeFourier_smul (c v) (fun t => F t v)) ξ
    rw [he, enorm_mul]
    exact (mul_le_mul' (hc v) le_rfl).trans (by
      simpa only [one_mul, Fourier.mixedFourierEnvelope00] using le_iSup
        (fun w => ‖Fourier.timeFourier (fun t => F t w) ξ‖ₑ) v)
  · rw [Fourier.mixedFourierNorm00_of_not_integrable hF]
    exact le_top

/-- The same estimate for the exact snapshot norm. -/
theorem XNorm00_output_mul_le {r : ℕ} {V : Type*}
    (s : ℝ) (F : (Fin r → ℝ) → V → ℂ) (c : V → ℂ)
    (hc : ∀ v, ‖c v‖ₑ ≤ 1) :
    XNorm00 s (fun t v => c v * F t v) ≤ XNorm00 s F := by
  simpa only [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00] using
    mixedFourierNorm00_output_mul_le s F c hc

end WaveTurbulence.Sumint
