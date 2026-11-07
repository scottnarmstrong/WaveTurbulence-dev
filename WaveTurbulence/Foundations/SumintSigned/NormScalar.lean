/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintSigned.NormModulation

/-!
# Exact scalar homogeneity for the general-output Fourier norm

The coefficient in each localized Fourier expansion is independent of
time and output. Homogeneity retains the integrability guard, including
the zero scalar and infinite norm cases.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintSigned

/-- Scalar multiplication factors exactly through the output Fourier envelope. -/
theorem mixedEnvelope00_smul {r : ℕ} {V : Type*} (c : ℂ)
    (F : (Fin r → ℝ) → V → ℂ) (ξ : Fin r → ℝ) :
    Fourier.mixedFourierEnvelope00 (fun t v => c • F t v) ξ =
      ‖c‖ₑ * Fourier.mixedFourierEnvelope00 F ξ := by
  unfold Fourier.mixedFourierEnvelope00
  simp_rw [Fourier.timeFourier_smul, enorm_smul]
  exact (ENNReal.mul_iSup ‖c‖ₑ (fun v => ‖Fourier.timeFourier (fun t => F t v) ξ‖ₑ)).symm

/-- Homogeneity is exact for arbitrary output carriers and all inputs. -/
theorem mixedFourierNorm00_smul {r : ℕ} {V : Type*} (s : ℝ) (c : ℂ)
    (F : (Fin r → ℝ) → V → ℂ) :
    Fourier.mixedFourierNorm00 s (fun t v => c • F t v) =
      ‖c‖ₑ * Fourier.mixedFourierNorm00 s F := by
  classical
  by_cases hc : c = 0
  · subst c
    simp
  have hi : (∀ v, Integrable (fun t => c • F t v)) ↔
      (∀ v, Integrable (fun t => F t v)) :=
    forall_congr' (fun v => integrable_smul_iff hc (fun t => F t v))
  unfold Fourier.mixedFourierNorm00
  rw [hi]
  split_ifs with hF
  · simp_rw [mixedEnvelope00_smul]
    calc
      _ = ∫⁻ ξ, ‖c‖ₑ * (Fourier.timeWeight s ξ * Fourier.mixedFourierEnvelope00 F ξ) := by
        apply lintegral_congr
        intro ξ
        ac_rfl
      _ = _ := lintegral_const_mul _ ((Fourier.timeWeight_measurable s).mul
        (Fourier.measurable_mixedFourierEnvelope00 hF))
  · simp [hc]

/-- Exact scalar homogeneity of the pre-freeze norm. -/
theorem XNorm00_smul {r : ℕ} {V : Type*} (s : ℝ) (c : ℂ)
    (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00 s (fun t v => c • F t v) = ‖c‖ₑ * XNorm00 s F := by
  simpa only [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00] using
    mixedFourierNorm00_smul s c F

end WaveTurbulence.SumintSigned
