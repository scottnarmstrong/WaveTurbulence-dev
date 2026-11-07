/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.DraftNormInterpolation
import Mathlib.Tactic

/-!
# Replacing a finite output supremum by a sum

This is the finite-output step preceding scalar Plancherel. The number
of outputs is bounded separately by the literal output lattice cover.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- A finite output supremum costs at most the sum of the scalar Fourier norms. -/
theorem mixedFourierNorm00_le_sum_scalar {r : ℕ} {V : Type*} [Fintype V] (θ : ℝ)
    (F : (Fin r → ℝ) → V → ℂ) (hF : ∀ v, Integrable (fun t => F t v)) :
    Fourier.mixedFourierNorm00 θ F ≤ ∑ v, Fourier.timeFourierNorm θ (fun t => F t v) := by
  classical
  rw [Fourier.mixedFourierNorm00_eq_lintegral hF]
  calc
    _ ≤ ∫⁻ ξ, ∑ v, Fourier.timeWeight θ ξ * ‖Fourier.timeFourier (fun t => F t v) ξ‖ₑ := by
      apply lintegral_mono
      intro ξ
      change Fourier.timeWeight θ ξ * (⨆ v, ‖Fourier.timeFourier (fun t => F t v) ξ‖ₑ) ≤
        ∑ v, Fourier.timeWeight θ ξ * ‖Fourier.timeFourier (fun t => F t v) ξ‖ₑ
      rw [← Finset.mul_sum]
      apply mul_le_mul_right
      apply iSup_le
      intro v
      exact Finset.single_le_sum (f := fun v => ‖Fourier.timeFourier (fun t => F t v) ξ‖ₑ) (fun _ _ => bot_le) (Finset.mem_univ v)
    _ = ∑ v, ∫⁻ ξ, Fourier.timeWeight θ ξ * ‖Fourier.timeFourier (fun t => F t v) ξ‖ₑ := by
      apply lintegral_finsetSum'
      intro v _
      exact ((Fourier.timeWeight_measurable θ).mul
        (Fourier.timeFourier_continuous (hF v)).measurable.enorm).aemeasurable
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      exact (Fourier.timeFourierNorm_eq_lintegral (hF v)).symm

/-- The same finite-output estimate holds for the exact draft norm. -/
theorem XNorm00_le_sum_scalar {r : ℕ} {V : Type*} [Fintype V] (θ : ℝ)
    (F : (Fin r → ℝ) → V → ℂ) (hF : ∀ v, Integrable (fun t => F t v)) :
    XNorm00 θ F ≤ ∑ v, Fourier.timeFourierNorm θ (fun t => F t v) := by
  rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
  exact mixedFourierNorm00_le_sum_scalar θ F hF

end WaveTurbulence.SumintPar
