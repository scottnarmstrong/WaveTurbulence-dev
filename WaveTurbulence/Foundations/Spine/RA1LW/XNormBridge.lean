/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge
public import WaveTurbulence.Foundations.Sumint.TimeBridge
public import WaveTurbulence.Foundations.Fourier.MixedNorm
public import WaveTurbulence.Foundations.Regref.TraceDeriv

/-!
# Snapshot 9's `XNorm` is the landed `mixedFourierNorm` (PL23-30D)

`XNorm θ Λ₁ Λ₂ F = Fourier.mixedFourierNorm θ Λ₁ Λ₂ F` at every order, for the F80 guard of snapshot 9: the
guards agree (`timeFT = mixedTimeFourier`), and where the frequency slices are `C^{Λ₁}` (almost everywhere) the
multi-index and coordinate-word suprema agree (`iterPartial` of the canonical word, and counts of a word).

* `XNorm_eq_mixedFourierNorm`, `XNormRestr_eq_rN`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace WaveTurbulence.RA1Leafwise

open WaveTurbulence.Fourier WaveTurbulence.NormBridgeScratch WaveTurbulence.Regref

variable {r d : ℕ}

theorem timeFT_eq_mixedTimeFourier' (F : (Fin r → ℝ) → Mom d → ℂ) (lam : Fin r → ℝ) :
    timeFT F lam = mixedTimeFourier F lam :=
  funext fun k => timeFT_eq_timeFourier F lam k

theorem ofReal_jbr_pow_mul (Λ₂ : ℕ) (k : Mom d) (z : ℂ) :
    ENNReal.ofReal (jbr k ^ Λ₂ * ‖z‖) = ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖z‖ₑ := by
  rw [ENNReal.ofReal_mul (show 0 ≤ jbr k ^ Λ₂ from pow_nonneg (Real.sqrt_nonneg _) _), ofReal_norm]
  rfl

theorem XNorm_eq_mixedFourierNorm (θ : ℝ) (Λ₁ Λ₂ : ℕ) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ Λ₁ Λ₂ F = mixedFourierNorm θ Λ₁ Λ₂ F := by
  classical
  by_cases hadm : MixedFourierAdmissible Λ₁ F
  · have hg : (∀ k, Integrable fun t => F t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam)) :=
      ⟨hadm.1, by simpa only [timeFT_eq_mixedTimeFourier'] using hadm.2⟩
    unfold XNorm
    rw [ite_eq_left hg, mixedFourierNorm_eq_iSup hadm]
    have hint : ∀ (ρ : Fin d → ℕ), ∫⁻ lam : Fin r → ℝ, maxBracketPow θ lam *
        ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (timeFT F lam) k‖) =
        ∫⁻ lam : Fin r → ℝ, timeWeight θ lam * momentumSupNorm Λ₂ (iterPartial ρ (mixedTimeFourier F lam)) := by
      intro ρ
      refine lintegral_congr fun lam => ?_
      rw [maxBracketPow_eq_timeWeight, timeFT_eq_mixedTimeFourier']
      congr 1
      unfold momentumSupNorm
      exact iSup_congr fun k => ofReal_jbr_pow_mul Λ₂ k _
    simp only [hint]
    by_cases hΛ : Λ₁ = 0
    · subst hΛ
      apply le_antisymm
      · refine iSup₂_le fun ρ hρ => ?_
        have hρ0 := (sum_le_zero_iff ρ).1 hρ
        subst hρ0
        simp only [iterPartial_zero]
        exact le_iSup₂_of_le 0 le_rfl (le_iSup_of_le Fin.elim0 (by simp only [momentumDerivative_zero]; exact le_rfl))
      · refine iSup₂_le fun n hn => iSup_le fun w => ?_
        have hn0 : n = 0 := by omega
        subst hn0
        refine le_iSup₂_of_le (0 : Fin d → ℕ) (by simp) ?_
        simp only [momentumDerivative_zero, iterPartial_zero]
        have : w = Fin.elim0 := Subsingleton.elim _ _
        subst this
        exact le_rfl
    · have hsm : ∀ᵐ lam, ContDiff ℝ Λ₁ (mixedTimeFourier F lam) := hadm.2.resolve_left hΛ
      apply le_antisymm
      · refine iSup₂_le fun ρ hρ => ?_
        have : ∫⁻ lam : Fin r → ℝ, timeWeight θ lam * momentumSupNorm Λ₂ (iterPartial ρ (mixedTimeFourier F lam)) =
            ∫⁻ lam : Fin r → ℝ, timeWeight θ lam * momentumSupNorm Λ₂
              (momentumDerivative (canonical ρ).get (mixedTimeFourier F lam)) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hsm] with lam hlam
          rw [iterPartial_eq_momentumDerivative_canonical ρ (hlam.of_le (by exact_mod_cast hρ))]
        rw [this]
        have hlen : (canonical ρ).length ≤ Λ₁ := by rw [canonical_length]; exact hρ
        exact le_iSup₂_of_le (canonical ρ).length hlen (le_iSup (fun σ : Fin (canonical ρ).length → Fin d =>
          ∫⁻ lam : Fin r → ℝ, timeWeight θ lam * momentumSupNorm Λ₂ (momentumDerivative σ (mixedTimeFourier F lam)))
          (canonical ρ).get)
      · refine iSup₂_le fun n hn => iSup_le fun w => ?_
        have : ∫⁻ lam : Fin r → ℝ, timeWeight θ lam * momentumSupNorm Λ₂ (momentumDerivative w (mixedTimeFourier F lam)) =
            ∫⁻ lam : Fin r → ℝ, timeWeight θ lam * momentumSupNorm Λ₂
              (iterPartial (fun j => (List.ofFn w).count j) (mixedTimeFourier F lam)) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hsm] with lam hlam
          rw [momentumDerivative_eq_iterPartial_counts w (hlam.of_le (by exact_mod_cast hn))]
        rw [this]
        exact le_iSup₂_of_le (fun j => (List.ofFn w).count j)
          (by simpa only [sum_counts, List.length_ofFn] using hn) le_rfl
  · have hg : ¬ ((∀ k, Integrable fun t => F t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam))) := by
      intro h
      exact hadm ⟨h.1, by simpa only [timeFT_eq_mixedTimeFourier'] using h.2⟩
    unfold XNorm
    rw [ite_eq_right hg, mixedFourierNorm_of_not_admissible hadm]

theorem XNormRestr_eq_mixedRestrictionNorm (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin r → ℝ))
    (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNormRestr θ Λ₁ Λ₂ B Set.univ F =
      mixedRestrictionNorm θ Λ₁ Λ₂ B Set.univ (fun (t : B) (k : (Set.univ : Set (Mom d))) => F t.1 k.1) := by
  rw [mixedRestrictionNorm_eq_agreement]
  unfold XNormRestr
  refine iInf_congr fun G => iInf_congr fun hG => ?_
  exact XNorm_eq_mixedFourierNorm θ Λ₁ Λ₂ G

end WaveTurbulence.RA1Leafwise
