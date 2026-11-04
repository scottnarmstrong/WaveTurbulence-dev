/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeBasic
public import WaveTurbulence.Foundations.Fourier.Norm00V

/-!
# Retaining the literal global garden sign

TARGET (incohproof2), (incohproof8)–(9), audit P-3. A garden's global unit
phase is carried as an actual multiplicative factor. It preserves the
weighted temporal and order-zero mixed norms exactly.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The source global sign/phase retained as an actual kernel factor. -/
@[expose] def gardenSignedKernel {T : Type*} (ζ : Circle) (K : T → ℂ) (t : T) : ℂ :=
  (ζ : ℂ) * K t

/-- A literal global garden sign preserves every weighted time Fourier norm. -/
theorem timeFourierNorm_gardenSignedKernel {r : ℕ} (ζ : Circle) (θ : ℝ)
    (K : (Fin r → ℝ) → ℂ) :
    Fourier.timeFourierNorm θ (gardenSignedKernel ζ K) = Fourier.timeFourierNorm θ K := by
  have hn : ‖(ζ : ℂ)‖ₑ = 1 := by rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]
  change Fourier.timeFourierNorm θ (fun t => (ζ : ℂ) * K t) = _
  simpa only [smul_eq_mul, hn, one_mul] using
    Fourier.timeFourierNorm_smul θ (ζ : ℂ) K

/-- The sign is also retained with the momentum supremum inside the frequency integral. -/
theorem mixedFourierNorm00_gardenSign {r : ℕ} {V : Type*} (ζ : Circle) (θ : ℝ)
    (K : (Fin r → ℝ) → V → ℂ) :
    Fourier.mixedFourierNorm00 θ (fun t v => (ζ : ℂ) * K t v) = Fourier.mixedFourierNorm00 θ K := by
  have hn : ‖(ζ : ℂ)‖ₑ = 1 := by rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]
  have hu : IsUnit (ζ : ℂ) := isUnit_iff_ne_zero.mpr (Circle.coe_ne_zero ζ)
  have hi : (∀ v, Integrable (fun t => (ζ : ℂ) * K t v)) ↔ ∀ v, Integrable (fun t => K t v) :=
    forall_congr' (fun v => integrable_const_mul_iff hu (fun t => K t v))
  by_cases hK : ∀ v, Integrable (fun t => K t v)
  · rw [Fourier.mixedFourierNorm00_eq_lintegral (hi.mpr hK), Fourier.mixedFourierNorm00_eq_lintegral hK]
    apply lintegral_congr
    intro ξ
    congr 1
    apply iSup_congr
    intro v
    change ‖Fourier.timeFourier (fun t => (ζ : ℂ) • K t v) ξ‖ₑ = _
    rw [Fourier.timeFourier_smul, enorm_smul, hn, one_mul]
  · rw [Fourier.mixedFourierNorm00_of_not_integrable hK,
      Fourier.mixedFourierNorm00_of_not_integrable (fun h => hK (hi.mp h))]

end WaveTurbulence.Incoh
