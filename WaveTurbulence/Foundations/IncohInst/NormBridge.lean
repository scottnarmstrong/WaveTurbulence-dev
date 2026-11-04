/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge
public import WaveTurbulence.Foundations.Fourier.MixedNorm

/-! # B2's exact norm is bounded by the analytic mixed norm, at every spatial weight -/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.IncohInst
open _root_.WaveTurbulence.Fourier NormBridgeScratch

variable {r d : ℕ}

/-- Equality of the literal B1 Fourier transform and the analytic Fourier transform. -/
theorem timeFT_eq_mixed (F : (Fin r → ℝ) → Mom d → ℂ) (lam : Fin r → ℝ) :
    timeFT F lam = mixedTimeFourier F lam :=
  funext fun k => timeFT_eq_timeFourier F lam k

/-- The exact B2 norm is no larger than the analytic norm, including the couple root weight. -/
theorem XNorm_le_mixed {J W : ℕ} (hJ : J ≠ 0) (θ : ℝ) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ J W F ≤ mixedFourierNorm θ J W F := by
  classical
  by_cases hadm : MixedFourierAdmissible J F
  · rw [mixedFourierNorm, ite_eq_left hadm]
    unfold XNorm
    have hsm := hadm.2.resolve_left hJ
    have hg : (∀ k, Integrable fun t => F t k) ∧ (J = 0 ∨ ∀ᵐ lam, ContDiff ℝ J (timeFT F lam)) :=
      ⟨hadm.1, Or.inr (by simpa only [timeFT_eq_mixed] using hsm)⟩
    rw [ite_eq_left hg]
    refine iSup₂_le fun ρ hρ => ?_
    have hlen : (canonical ρ).length ≤ J := by rw [canonical_length]; exact hρ
    refine le_iSup₂_of_le (canonical ρ).length hlen (le_iSup_of_le (canonical ρ).get
      (le_of_eq (lintegral_congr_ae ?_)))
    filter_upwards [hsm] with lam hlam
    rw [maxBracketPow_eq_timeWeight, timeFT_eq_mixed]
    congr 1
    refine iSup_congr fun k => ?_
    rw [iterPartial_eq_momentumDerivative_canonical ρ (hlam.of_le (by exact_mod_cast hρ))]
    rw [ENNReal.ofReal_mul (show 0 ≤ jbr k ^ W from pow_nonneg (Real.sqrt_nonneg _) _), ofReal_norm]
    rfl
  · rw [mixedFourierNorm, ite_eq_right hadm]
    exact le_top

/-- The exact restriction formulation consumed by B2 follows without changing its domain. -/
theorem XNormRestr_le_mixed {J W : ℕ} (hJ : J ≠ 0) (θ : ℝ) (B : Set (Fin r → ℝ))
    (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNormRestr θ J W B K F ≤ mixedRestrictionNorm θ J W B K (fun t k => F t k) := by
  unfold mixedRestrictionNorm
  apply le_iInf
  intro G
  apply le_iInf
  intro hG
  apply (iInf₂_le_of_le G ?_ (le_refl (XNorm θ J W G))).trans (XNorm_le_mixed hJ θ G)
  intro t ht k hk
  exact hG ⟨t, ht⟩ ⟨k, hk⟩

end WaveTurbulence.IncohInst
