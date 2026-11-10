/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Sumint.MultiIndices
public import WaveTurbulence.Foundations.Sumint.TimeBridge
/-! Universal spatial norm bridges after the authorized order-zero guard correction. -/
public section
namespace WaveTurbulence.NormBridgeScratch
open Finset
open scoped Classical ENNReal

theorem derivativeSup_eq {d N : ℕ} {f : Mom d → ℂ} (hf : ContDiff ℝ N f)
    (Q : (Mom d → ℂ) → ℝ≥0∞) :
    (⨆ (ρ : Fin d → ℕ) (_ : ∑ j, ρ j ≤ N), Q (iterPartial ρ f)) =
      ⨆ (n : ℕ) (_ : n ≤ N) (ρ : Fin n → Fin d), Q (Fourier.momentumDerivative ρ f) := by
  apply le_antisymm
  · apply iSup_le
    intro ρ
    apply iSup_le
    intro hρ
    rw [iterPartial_eq_momentumDerivative_canonical ρ (hf.of_le (by exact_mod_cast hρ))]
    exact le_iSup_of_le (canonical ρ).length (le_iSup_of_le
      (by simpa only [canonical_length] using hρ) (le_iSup (fun σ : Fin (canonical ρ).length → Fin d => Q (Fourier.momentumDerivative σ f)) (canonical ρ).get))
  · apply iSup_le
    intro n
    apply iSup_le
    intro hn
    apply iSup_le
    intro ρ
    rw [momentumDerivative_eq_iterPartial_counts ρ (hf.of_le (by exact_mod_cast hn))]
    exact le_iSup_of_le (fun j => (List.ofFn ρ).count j)
      (le_iSup_of_le (by simpa only [sum_counts, List.length_ofFn] using hn) le_rfl)

theorem SNorm_eq_spatialNorm_of_contDiff {d Λ₁ Λ₂ : ℕ} {F : Mom d → ℂ}
    (hF : ContDiff ℝ Λ₁ F) : SNorm Λ₁ Λ₂ F = Fourier.spatialNorm Λ₁ Λ₂ F := by
  have hw (k : Mom d) (z : ℂ) : ENNReal.ofReal (jbr k ^ Λ₂ * ‖z‖) =
      ENNReal.ofReal (Fourier.momentumBracket k ^ Λ₂) * ‖z‖ₑ := by
    rw [ENNReal.ofReal_mul (show 0 ≤ jbr k ^ Λ₂ from pow_nonneg (Real.sqrt_nonneg _) _), ofReal_norm]
    rfl
  simp only [SNorm, Fourier.spatialNorm, ite_eq_left (Or.inr hF)]
  simp_rw [hw]
  exact derivativeSup_eq hF (Fourier.momentumSupNorm Λ₂)


/-- TARGET normX2: exact equality at all derivative orders, including discontinuous order-zero inputs. -/
theorem SNorm_eq_spatialNorm {d Λ₁ Λ₂ : ℕ} (F : Mom d → ℂ) :
    SNorm Λ₁ Λ₂ F = Fourier.spatialNorm Λ₁ Λ₂ F := by
  by_cases hΛ : Λ₁ = 0
  · subst Λ₁
    rw [Fourier.spatialNorm_zero_order]
    simp only [SNorm, Nat.cast_zero, true_or, ite_true, sum_le_zero_iff,
      iSup_iSup_eq_left, iterPartial_zero]
    unfold Fourier.momentumSupNorm
    apply iSup_congr
    intro k
    rw [ENNReal.ofReal_mul (show 0 ≤ jbr k ^ Λ₂ from pow_nonneg (Real.sqrt_nonneg _) _), ofReal_norm]
    rfl
  · by_cases hF : ContDiff ℝ Λ₁ F
    · exact SNorm_eq_spatialNorm_of_contDiff hF
    · simp only [SNorm, Fourier.spatialNorm, hΛ, false_or, hF, ite_false]

/-- The real norm uses exactly the same complex embedding as the landed spatial norm. -/
theorem SNormR_eq_spatialNorm {d Λ₁ Λ₂ : ℕ} (F : Mom d → ℝ) :
    SNormR Λ₁ Λ₂ F = Fourier.spatialNorm Λ₁ Λ₂ (fun k => (F k : ℂ)) :=
  SNorm_eq_spatialNorm _

end WaveTurbulence.NormBridgeScratch
