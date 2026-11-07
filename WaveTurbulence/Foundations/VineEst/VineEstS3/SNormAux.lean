/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSNorm

/-! # Scalar multiples and zero in `SNorm` -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.NormBridgeScratch MeasureTheory Set
open scoped ENNReal ContDiff

variable {d : ℕ}

theorem momentumDerivative_const_mul {n N : ℕ} (hn : n ≤ N) (σ : Fin n → Fin d) (c : ℂ)
    {f : Mom d → ℂ} (hf : ContDiff ℝ N f) (k : Mom d) :
    momentumDerivative σ (fun k => c * f k) k = c * momentumDerivative σ f k := by
  unfold momentumDerivative
  have h1 : iteratedFDeriv ℝ n (fun k => c * f k) k = c • iteratedFDeriv ℝ n f k := by
    have := Layered.iteratedFDeriv_const_mul_param hf c (by exact_mod_cast hn) k
    simpa only [mul_comm] using this
  rw [h1]
  simp

theorem SNorm_smul_le (Λ₁ Λ₂ : ℕ) (c : ℂ) (f : Mom d → ℂ) :
    SNorm Λ₁ Λ₂ (fun k => c * f k) ≤ ‖c‖ₑ * SNorm Λ₁ Λ₂ f := by
  rw [SNorm_eq_spatialNorm, SNorm_eq_spatialNorm]
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, enorm_zero, zero_mul]
    unfold spatialNorm
    rw [ite_eq_left (Or.inr contDiff_const)]
    refine iSup₂_le fun n hn => iSup_le fun σ => ?_
    unfold momentumSupNorm
    refine iSup_le fun k => ?_
    cases n with
    | zero => simp
    | succ n => simp [momentumDerivative, iteratedFDeriv_succ_const]
  · by_cases hg : Λ₁ = 0 ∨ ContDiff ℝ Λ₁ f
    · have hg' : Λ₁ = 0 ∨ ContDiff ℝ Λ₁ (fun k => c * f k) := by
        rcases hg with h | h
        · exact Or.inl h
        · exact Or.inr (contDiff_const.mul h)
      unfold spatialNorm
      rw [ite_eq_left hg', ite_eq_left hg]
      refine iSup₂_le fun n hn => iSup_le fun σ => ?_
      refine le_trans ?_ (mul_le_mul_right (le_iSup₂_of_le n hn (le_iSup (fun σ : Fin n → Fin d =>
        momentumSupNorm Λ₂ (momentumDerivative σ f)) σ)) ‖c‖ₑ)
      unfold momentumSupNorm
      rw [ENNReal.mul_iSup]
      refine iSup_le fun k => le_iSup_of_le k ?_
      have hd : momentumDerivative σ (fun k => c * f k) k = c * momentumDerivative σ f k := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp
        · have hΛ : Λ₁ ≠ 0 := by omega
          exact momentumDerivative_const_mul hn σ c (hg.resolve_left hΛ) k
      rw [hd, enorm_mul]
      calc ENNReal.ofReal (momentumBracket k ^ Λ₂) * (‖c‖ₑ * ‖momentumDerivative σ f k‖ₑ)
          = ‖c‖ₑ * (ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖momentumDerivative σ f k‖ₑ) := by ring
        _ ≤ _ := le_rfl
    · have : spatialNorm Λ₁ Λ₂ f = ⊤ := by
        unfold spatialNorm; exact ite_eq_right hg
      rw [this, ENNReal.mul_top (by simpa using hc)]
      exact le_top

theorem eq_zero_of_SNorm_eq_zero {Λ₁ Λ₂ : ℕ} {f : Mom d → ℂ} (h : SNorm Λ₁ Λ₂ f = 0) : f = 0 := by
  rw [SNorm_eq_spatialNorm] at h
  by_cases hg : Λ₁ = 0 ∨ ContDiff ℝ Λ₁ f
  · unfold spatialNorm at h
    rw [ite_eq_left hg] at h
    funext k
    have h0 := (iSup₂_eq_bot.1 (le_bot_iff.1 h.le)) 0 (Nat.zero_le _)
    have h1 := (iSup_eq_bot.1 h0) (Fin.elim0 : Fin 0 → Fin d)
    have h2 : ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖momentumDerivative (Fin.elim0 : Fin 0 → Fin d) f k‖ₑ = 0 :=
      (iSup_eq_bot.1 h1) k
    rw [momentumDerivative_zero] at h2
    rcases mul_eq_zero.1 h2 with h2 | h2
    · exfalso
      have : ENNReal.ofReal (momentumBracket k ^ Λ₂) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact pow_pos (lt_of_lt_of_le zero_lt_one (FS.one_le_momentumBracket k)) _
      exact this h2
    · exact enorm_eq_zero.1 h2
  · unfold spatialNorm at h
    rw [ite_eq_right hg] at h
    exact absurd h (by simp)

end WaveTurbulence.VineEstS3.Eng
