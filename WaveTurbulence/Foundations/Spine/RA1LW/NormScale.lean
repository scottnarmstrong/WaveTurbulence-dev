/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.MixedNorm
public import WaveTurbulence.Foundations.Fourier.TimeBasic

/-! # Scalar homogeneity of the mixed norm with momentum derivatives (RA1-LEAFWISE) -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open MeasureTheory Set WaveTurbulence.Fourier
open scoped ENNReal

variable {r d : ℕ}

theorem mixedTimeFourier_smul (c : ℂ) (F : (Fin r → ℝ) → Mom d → ℂ) (ξ : Fin r → ℝ) :
    mixedTimeFourier (fun t k => c • F t k) ξ = fun k => c • mixedTimeFourier F ξ k := by
  funext k
  unfold mixedTimeFourier
  exact congrFun (timeFourier_smul c (fun t => F t k)) ξ

theorem momentumSupNorm_smul (Λ : ℕ) (c : ℂ) (f : Mom d → ℂ) :
    momentumSupNorm Λ (fun k => c • f k) = ‖c‖ₑ * momentumSupNorm Λ f := by
  unfold momentumSupNorm
  simp only [enorm_smul]
  simp_rw [mul_left_comm (ENNReal.ofReal _) ‖c‖ₑ]
  rw [← ENNReal.mul_iSup]

theorem contDiff_smul_iff {c : ℂ} (hc : c ≠ 0) {n : WithTop ℕ∞} {f : Mom d → ℂ} :
    ContDiff ℝ n (fun k => c • f k) ↔ ContDiff ℝ n f := by
  constructor
  · intro h
    have := h.const_smul c⁻¹
    simpa only [inv_smul_smul₀ hc] using this
  · intro h
    exact h.const_smul c

theorem momentumDerivative_smul {n : ℕ} (ρ : Fin n → Fin d) (c : ℂ) {f : Mom d → ℂ}
    (hf : ContDiff ℝ n f) :
    momentumDerivative ρ (fun k => c • f k) = fun k => c • momentumDerivative ρ f k := by
  funext k
  unfold momentumDerivative
  rw [iteratedFDeriv_const_smul_apply' hf.contDiffAt]
  rfl

theorem admissible_smul_iff {c : ℂ} (hc : c ≠ 0) (Λ₁ : ℕ) (F : (Fin r → ℝ) → Mom d → ℂ) :
    MixedFourierAdmissible Λ₁ (fun t k => c • F t k) ↔ MixedFourierAdmissible Λ₁ F := by
  unfold MixedFourierAdmissible
  have h1 : (∀ k, Integrable (fun t => c • F t k)) ↔ ∀ k, Integrable (fun t => F t k) :=
    forall_congr' fun k => integrable_smul_iff hc _
  have h2 : (Λ₁ = 0 ∨ ∀ᵐ ξ, ContDiff ℝ Λ₁ (mixedTimeFourier (fun t k => c • F t k) ξ)) ↔
      (Λ₁ = 0 ∨ ∀ᵐ ξ, ContDiff ℝ Λ₁ (mixedTimeFourier F ξ)) := by
    refine or_congr Iff.rfl ?_
    simp only [mixedTimeFourier_smul]
    constructor
    · intro h
      filter_upwards [h] with ξ hξ
      exact (contDiff_smul_iff hc).mp hξ
    · intro h
      filter_upwards [h] with ξ hξ
      exact (contDiff_smul_iff hc).mpr hξ
  rw [h1, h2]

/-- Exact scalar homogeneity of the mixed norm for a nonzero constant. -/
theorem mixedFourierNorm_smul {c : ℂ} (hc : c ≠ 0) (θ : ℝ) (Λ₁ Λ₂ : ℕ)
    (F : (Fin r → ℝ) → Mom d → ℂ) :
    mixedFourierNorm θ Λ₁ Λ₂ (fun t k => c • F t k) = ‖c‖ₑ * mixedFourierNorm θ Λ₁ Λ₂ F := by
  classical
  have hc0 : ‖c‖ₑ ≠ 0 := by simpa using hc
  have hct : ‖c‖ₑ ≠ ⊤ := enorm_ne_top
  by_cases hadm : MixedFourierAdmissible Λ₁ F
  · have hadm' := (admissible_smul_iff hc Λ₁ F).mpr hadm
    unfold mixedFourierNorm
    rw [if_pos hadm', if_pos hadm]
    have key : ∀ᵐ ξ : Fin r → ℝ, ∀ n : ℕ, n ≤ Λ₁ → ∀ ρ : Fin n → Fin d,
        momentumDerivative ρ (mixedTimeFourier (fun t k => c • F t k) ξ) =
          fun k => c • momentumDerivative ρ (mixedTimeFourier F ξ) k := by
      by_cases h0 : Λ₁ = 0
      · refine Filter.Eventually.of_forall fun ξ n hn ρ => ?_
        have : n = 0 := by omega
        subst this
        simp only [momentumDerivative_zero, mixedTimeFourier_smul]
      · have hsm := hadm.2.resolve_left h0
        filter_upwards [hsm] with ξ hξ n hn ρ
        rw [mixedTimeFourier_smul]
        exact momentumDerivative_smul ρ c (hξ.of_le (by exact_mod_cast hn))
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun n => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun hn => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun ρ => ?_
    calc ∫⁻ ξ, timeWeight θ ξ * momentumSupNorm Λ₂
          (momentumDerivative ρ (mixedTimeFourier (fun t k => c • F t k) ξ))
        = ∫⁻ ξ, ‖c‖ₑ * (timeWeight θ ξ * momentumSupNorm Λ₂
          (momentumDerivative ρ (mixedTimeFourier F ξ))) := by
          refine lintegral_congr_ae ?_
          filter_upwards [key] with ξ hξ
          rw [hξ n hn ρ, momentumSupNorm_smul]
          ring
      _ = _ := lintegral_const_mul' _ _ hct
  · have hadm' : ¬ MixedFourierAdmissible Λ₁ (fun t k => c • F t k) := fun h =>
      hadm ((admissible_smul_iff hc Λ₁ F).mp h)
    rw [mixedFourierNorm_of_not_admissible hadm, mixedFourierNorm_of_not_admissible hadm']
    exact (ENNReal.mul_top hc0).symm

/-- Homogeneity (inequality form) of the restriction norm for a nonzero constant. -/
theorem mixedRestrictionNorm_smul_le {c : ℂ} (hc : c ≠ 0) (θ : ℝ) (Λ₁ Λ₂ : ℕ)
    (B : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : B → K → ℂ) :
    mixedRestrictionNorm θ Λ₁ Λ₂ B K (fun t k => c • F t k) ≤
      ‖c‖ₑ * mixedRestrictionNorm θ Λ₁ Λ₂ B K F := by
  have hc0 : ‖c‖ₑ ≠ 0 := by simpa using hc
  have hct : ‖c‖ₑ ≠ ⊤ := enorm_ne_top
  unfold mixedRestrictionNorm
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  refine le_iInf fun G => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  refine le_iInf fun hG => ?_
  exact iInf_le_of_le (fun t k => c • G t k) (iInf_le_of_le (fun t k => by simp only [hG t k])
    (mixedFourierNorm_smul hc θ Λ₁ Λ₂ G).le)

end WaveTurbulence.RA1Leafwise
