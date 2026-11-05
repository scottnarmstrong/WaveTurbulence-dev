/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Regref.TraceDeriv
public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge

/-!
# B2's `𝔛` norms are bounded by the landed TARGET (normX) norms (positive derivative order)

B2's `XNorm θ Λ 0` puts `⊤` in the frequency integrand at the frequencies where `k ↦ F̂(λ, k)` is not `C^Λ`; the
landed `Fourier.mixedFourierNorm θ Λ 0` requires that smoothness almost everywhere (WAVE-B §2.6). On the smooth
frequencies the integrands agree (`iterPartial` = coordinate words, `NormBridgeScratch`), so
`XNorm ≤ mixedFourierNorm` (`XNorm_le_mixedFourierNorm`) and the same for the restriction norms
(`XNormRestr_le_mixedRestrictionNorm`). (The zero-order equalities are `NormBridgeScratch.XNorm_zero_order_eq_…`.)
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Regref

open WaveTurbulence.Fourier NormBridgeScratch

variable {r d : ℕ}

theorem timeFT_eq_mixedTimeFourier (F : (Fin r → ℝ) → Mom d → ℂ) (lam : Fin r → ℝ) :
    timeFT F lam = mixedTimeFourier F lam :=
  funext fun k => timeFT_eq_timeFourier F lam k

/-- **`XNorm θ Λ 0 ≤ mixedFourierNorm θ Λ 0`** for `Λ ≥ 1`. -/
theorem XNorm_le_mixedFourierNorm {Λ : ℕ} (hΛ : Λ ≠ 0) (θ : ℝ) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ Λ 0 F ≤ mixedFourierNorm θ Λ 0 F := by
  classical
  by_cases hadm : MixedFourierAdmissible Λ F
  · rw [mixedFourierNorm_eq_iSup hadm]
    unfold XNorm
    have hsm := hadm.2.resolve_left hΛ
    have hg : (∀ k, Integrable fun t => F t k) ∧ (Λ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ (timeFT F lam)) :=
      ⟨hadm.1, Or.inr (by simpa only [timeFT_eq_mixedTimeFourier] using hsm)⟩
    rw [ite_eq_left hg]
    refine iSup₂_le fun ρ hρ => ?_
    have hlen : (canonical ρ).length ≤ Λ := by rw [canonical_length]; exact hρ
    refine le_iSup₂_of_le (canonical ρ).length hlen (le_iSup_of_le (canonical ρ).get
      (le_of_eq (lintegral_congr_ae ?_)))
    filter_upwards [hsm] with lam hlam
    rw [maxBracketPow_eq_timeWeight, timeFT_eq_mixedTimeFourier, momentumSupNorm_zero_eq]
    congr 1
    refine iSup_congr fun k => ?_
    rw [iterPartial_eq_momentumDerivative_canonical ρ (hlam.of_le (by exact_mod_cast hρ)), pow_zero,
      one_mul, ofReal_norm]
  · rw [mixedFourierNorm_of_not_admissible hadm]
    exact le_top

/-- **`XNormRestr θ Λ 0 ≤ mixedRestrictionNorm θ Λ 0`** for `Λ ≥ 1`. -/
theorem XNormRestr_le_mixedRestrictionNorm {Λ : ℕ} (hΛ : Λ ≠ 0) (θ : ℝ) (B : Set (Fin r → ℝ))
    (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNormRestr θ Λ 0 B K F ≤ mixedRestrictionNorm θ Λ 0 B K (fun t k => F t k) := by
  rw [mixedRestrictionNorm_eq_agreement]
  unfold XNormRestr
  exact iInf₂_mono fun G _ => XNorm_le_mixedFourierNorm hΛ θ G

/-- **`XNorm θ Λ Λ₂ ≤ mixedFourierNorm θ Λ Λ₂`** (general weight; B21-SNAP9) for `Λ ≥ 1`. -/
theorem XNorm_le_mixedFourierNorm' {Λ : ℕ} (Λ₂ : ℕ) (hΛ : Λ ≠ 0) (θ : ℝ) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ Λ Λ₂ F ≤ mixedFourierNorm θ Λ Λ₂ F := by
  classical
  by_cases hadm : MixedFourierAdmissible Λ F
  · rw [mixedFourierNorm_eq_iSup hadm]
    unfold XNorm
    have hsm := hadm.2.resolve_left hΛ
    have hg : (∀ k, Integrable fun t => F t k) ∧ (Λ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ (timeFT F lam)) :=
      ⟨hadm.1, Or.inr (by simpa only [timeFT_eq_mixedTimeFourier] using hsm)⟩
    rw [ite_eq_left hg]
    refine iSup₂_le fun ρ hρ => ?_
    have hlen : (canonical ρ).length ≤ Λ := by rw [canonical_length]; exact hρ
    refine le_iSup₂_of_le (canonical ρ).length hlen (le_iSup_of_le (canonical ρ).get
      (le_of_eq (lintegral_congr_ae ?_)))
    filter_upwards [hsm] with lam hlam
    rw [maxBracketPow_eq_timeWeight, timeFT_eq_mixedTimeFourier]
    unfold momentumSupNorm
    congr 1
    refine iSup_congr fun k => ?_
    rw [iterPartial_eq_momentumDerivative_canonical ρ (hlam.of_le (by exact_mod_cast hρ)),
      ← ofReal_norm]
    exact ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg (1 + ‖k‖ ^ 2)) Λ₂)
  · rw [mixedFourierNorm_of_not_admissible hadm]
    exact le_top

/-- **`XNormRestr θ Λ Λ₂ ≤ mixedRestrictionNorm θ Λ Λ₂`** (general weight) for `Λ ≥ 1`. -/
theorem XNormRestr_le_mixedRestrictionNorm' {Λ : ℕ} (Λ₂ : ℕ) (hΛ : Λ ≠ 0) (θ : ℝ) (B : Set (Fin r → ℝ))
    (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNormRestr θ Λ Λ₂ B K F ≤ mixedRestrictionNorm θ Λ Λ₂ B K (fun t k => F t k) := by
  rw [mixedRestrictionNorm_eq_agreement]
  unfold XNormRestr
  exact iInf₂_mono fun G _ => XNorm_le_mixedFourierNorm' Λ₂ hΛ θ G

end WaveTurbulence.Regref
