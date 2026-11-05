/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.TraceW

/-!
# Time translations in `𝔛^{θ,Λ,Λ₂}` (PL23-30D)

`mixedFourierNorm_translate`: `𝔛^{θ,Λ,Λ₂}(F(· + a)) = 𝔛^{θ,Λ,Λ₂}(F)`, the transform changes by a unit phase.
`rN_translate_le`: the restriction norm version.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ}

theorem contDiff_const_mul_iff' {Λ : ℕ} {u : ℂ} (hu : u ≠ 0) (f : Mom d → ℂ) :
    ContDiff ℝ Λ (fun k => u * f k) ↔ ContDiff ℝ Λ f := by
  constructor
  · intro h
    have e : f = fun k => u⁻¹ • (u * f k) := by
      funext k
      simp [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hu]
    rw [e]
    exact h.const_smul u⁻¹
  · intro h
    exact h.const_smul u

theorem momentumDerivative_const_mul {Λ n : ℕ} (hn : n ≤ Λ) (ρ : Fin n → Fin d) (u : ℂ) {f : Mom d → ℂ}
    (hf : ContDiff ℝ Λ f) :
    momentumDerivative ρ (fun k => u * f k) = fun k => u * momentumDerivative ρ f k := by
  funext k
  unfold momentumDerivative
  have h := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := n) (a := u) (f := f) (x := k)
    (hf.contDiffAt.of_le (by exact_mod_cast hn))
  have h' : iteratedFDeriv ℝ n (fun k => u * f k) k = u • iteratedFDeriv ℝ n f k := h
  rw [h']
  simp

theorem momentumSupNorm_const_mul_unit (Λ₂ : ℕ) {u : ℂ} (hu : ‖u‖ = 1) (f : Mom d → ℂ) :
    momentumSupNorm Λ₂ (fun k => u * f k) = momentumSupNorm Λ₂ f := by
  unfold momentumSupNorm
  refine iSup_congr fun k => ?_
  rw [enorm_mul, ← ofReal_norm u, hu, ENNReal.ofReal_one, one_mul]

theorem mixedFourierNorm_translate (θ : ℝ) (Λ Λ₂ : ℕ) (F : (Fin r → ℝ) → Mom d → ℂ) (a : Fin r → ℝ) :
    mixedFourierNorm θ Λ Λ₂ (fun t k => F (t + a) k) = mixedFourierNorm θ Λ Λ₂ F := by
  have hi : ∀ k, (Integrable (fun t => F (t + a) k)) ↔ Integrable (fun t => F t k) := fun k => by
    constructor
    · intro h
      simpa only [add_assoc, neg_add_cancel, add_zero] using h.comp_add_right (-a)
    · intro h
      exact h.comp_add_right a
  set u : (Fin r → ℝ) → ℂ := fun ξ => ((Real.fourierChar (timePairing r a ξ) : Circle) : ℂ) with hu
  have hunit : ∀ ξ, ‖u ξ‖ = 1 := fun ξ => Circle.norm_coe _
  have hu0 : ∀ ξ, u ξ ≠ 0 := fun ξ h => by
    have := hunit ξ
    rw [h] at this
    simp at this
  have hFT : ∀ ξ, mixedTimeFourier (fun t k => F (t + a) k) ξ = fun k => u ξ * mixedTimeFourier F ξ k := by
    intro ξ
    funext k
    unfold mixedTimeFourier
    have := congrFun (timeFourier_translate (fun t => F t k) a) ξ
    simpa [hu, smul_eq_mul, Circle.smul_def] using this
  by_cases hadm : MixedFourierAdmissible Λ F
  · have hadm' : MixedFourierAdmissible Λ (fun t k => F (t + a) k) := by
      refine ⟨fun k => (hi k).2 (hadm.1 k), ?_⟩
      rcases hadm.2 with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        filter_upwards [h] with ξ hξ
        rw [hFT ξ]
        exact (contDiff_const_mul_iff' (hu0 ξ) _).2 hξ
    rw [mixedFourierNorm_eq_iSup hadm', mixedFourierNorm_eq_iSup hadm]
    refine iSup_congr fun n => iSup_congr fun hn => iSup_congr fun ρ => ?_
    refine lintegral_congr_ae ?_
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      exact Eventually.of_forall fun ξ => by
        simp only [momentumDerivative_zero]
        rw [hFT ξ, momentumSupNorm_const_mul_unit Λ₂ (hunit ξ)]
    · have hsm : ∀ᵐ ξ, ContDiff ℝ Λ (mixedTimeFourier F ξ) := by
        rcases hadm.2 with h | h
        · omega
        · exact h
      filter_upwards [hsm] with ξ hξ
      rw [hFT ξ, momentumDerivative_const_mul hn ρ (u ξ) hξ, momentumSupNorm_const_mul_unit Λ₂ (hunit ξ)]
  · have hadm' : ¬ MixedFourierAdmissible Λ (fun t k => F (t + a) k) := by
      intro h
      apply hadm
      refine ⟨fun k => (hi k).1 (h.1 k), ?_⟩
      rcases h.2 with h2 | h2
      · exact Or.inl h2
      · refine Or.inr ?_
        filter_upwards [h2] with ξ hξ
        rw [hFT ξ] at hξ
        exact (contDiff_const_mul_iff' (hu0 ξ) _).1 hξ
    rw [mixedFourierNorm_of_not_admissible hadm, mixedFourierNorm_of_not_admissible hadm']

theorem rN_translate_le {θ : ℝ} {Λ Λ₂ : ℕ} {B B' : Set (Fin r → ℝ)} (h : (Fin r → ℝ) → Mom d → ℂ)
    (a : Fin r → ℝ) (hBB : ∀ t ∈ B, t + a ∈ B') :
    rN θ Λ Λ₂ B (fun t k => h (t + a) k) ≤ rN θ Λ Λ₂ B' h := by
  rw [rN_eq_agreement B, rN_eq_agreement B' h]
  refine le_iInf₂ fun G hG => ?_
  refine (iInf₂_le (fun t k => G (t + a) k) fun t ht k hk => hG _ (hBB t ht) k hk).trans ?_
  exact (mixedFourierNorm_translate θ Λ Λ₂ G a).le

end WaveTurbulence.PL2330
