/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.MixedNorm

/-! # The source mixed norm is bounded by its full spatial frequency envelope -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- A fixed actual derivative component never exceeds the full source spatial norm. -/
theorem momentumSupNorm_derivative_le_spatialNorm {d N M j : ℕ}
    (f : Mom d → ℂ) (hj : j ≤ N) (ρ : Fin j → Fin d) :
    Fourier.momentumSupNorm M (Fourier.momentumDerivative ρ f) ≤ Fourier.spatialNorm N M f := by
  classical
  by_cases h : N = 0 ∨ ContDiff ℝ N f
  · rw [Fourier.spatialNorm, ite_eq_left h]
    exact le_iSup_of_le j (le_iSup_of_le hj (le_iSup_of_le ρ le_rfl))
  · rw [Fourier.spatialNorm, ite_eq_right h]
    exact le_top

/-- A finite positive-order source spatial norm includes its actual finite smoothness. -/
theorem contDiff_of_spatialNorm_lt_top {d N M : ℕ} {f : Mom d → ℂ}
    (hN : 0 < N) (h : Fourier.spatialNorm N M f < ⊤) : ContDiff ℝ N f := by
  by_contra hc
  have hn : ¬(N = 0 ∨ ContDiff ℝ N f) := by
    rintro (hz | hs)
    · omega
    · exact hc hs
  rw [Fourier.spatialNorm, ite_eq_right hn] at h
  exact (lt_irrefl _) h

/-- Conditional envelope transport retaining the actual momentum supremum inside the time
frequency integral. Admissibility is the defining typing condition of the source norm. -/
theorem mixedFourierNorm_le_lintegral_spatialNorm {r d N M : ℕ} (θ : ℝ)
    (F : (Fin r → ℝ) → Mom d → ℂ) (hF : Fourier.MixedFourierAdmissible N F) :
    Fourier.mixedFourierNorm θ N M F ≤
      ∫⁻ ξ, Fourier.timeWeight θ ξ * Fourier.spatialNorm N M (Fourier.mixedTimeFourier F ξ) := by
  rw [Fourier.mixedFourierNorm, ite_eq_left hF]
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  apply iSup_le
  intro ρ
  exact lintegral_mono (fun ξ => mul_le_mul' le_rfl
    (momentumSupNorm_derivative_le_spatialNorm (Fourier.mixedTimeFourier F ξ) hj ρ))

end WaveTurbulence.Incoh
