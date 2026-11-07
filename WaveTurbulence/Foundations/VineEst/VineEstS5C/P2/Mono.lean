/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Space
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ThetaMono

/-! # P2: monotonicity of `XNorm`/`XNormRestr` in the derivative index and the weight index (step 4)

`XNorm_mono_deriv`: `XNorm θ Λ₁' Λ₂ ≤ XNorm θ Λ₁ Λ₂` for `Λ₁' ≤ Λ₁`; `XNorm_mono_weight` likewise in `Λ₂`.  Hence
`XNormRestr_mono_idx`.  `snorm_lower`: `SNormR (30d)(30d)` bound of a real function gives the `SNorm A W` bound
of its complexification for `A, W ≤ 30 d` (the ambient rows are lowered from `30d` to the datum's `wN`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence MeasureTheory
open scoped ENNReal

variable {d : ℕ}

open Classical in
theorem XNorm_mono_idx {r : ℕ} {θ : ℝ} {Λ₁ Λ₁' Λ₂ Λ₂' : ℕ} (h1 : Λ₁' ≤ Λ₁) (h2 : Λ₂' ≤ Λ₂)
    (F : (Fin r → ℝ) → Mom d → ℂ) : XNorm θ Λ₁' Λ₂' F ≤ XNorm θ Λ₁ Λ₂ F := by
  by_cases hc' : (∀ k, Integrable fun t => F t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam))
  · have hc : (∀ k, Integrable fun t => F t k) ∧ (Λ₁' = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁' (timeFT F lam)) := by
      refine ⟨hc'.1, ?_⟩
      rcases hc'.2 with h0 | hd
      · exact Or.inl (by omega)
      · rcases Nat.eq_zero_or_pos Λ₁' with h0 | hp
        · exact Or.inl h0
        · exact Or.inr (hd.mono fun lam hl => hl.of_le (by exact_mod_cast h1))
    unfold XNorm
    rw [if_pos hc, if_pos hc']
    refine iSup₂_mono' fun ρ hρ => ⟨ρ, hρ.trans h1, lintegral_mono fun lam => ?_⟩
    refine mul_le_mul_right (iSup_mono fun k => ENNReal.ofReal_le_ofReal ?_) _
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (Induct.one_le_jbr k) h2) (norm_nonneg _)
  · have : XNorm θ Λ₁ Λ₂ F = ⊤ := by unfold XNorm; rw [if_neg hc']
    rw [this]; exact le_top

theorem XNormRestr_mono_idx {r : ℕ} {θ : ℝ} {Λ₁ Λ₁' Λ₂ Λ₂' : ℕ} (h1 : Λ₁' ≤ Λ₁) (h2 : Λ₂' ≤ Λ₂)
    (B : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNormRestr θ Λ₁' Λ₂' B K F ≤ XNormRestr θ Λ₁ Λ₂ B K F := by
  unfold XNormRestr
  refine le_iInf₂ fun G hG => ?_
  exact (iInf₂_le G hG).trans (XNorm_mono_idx h1 h2 G)

/-- Lowering the indices of the `𝔖`-bound of a real function. -/
theorem snorm_lower {Λ₁ Λ₂ A W : ℕ} (hΛ : Λ₁ ≠ 0) (hA : A ≤ Λ₁) (hW : W ≤ Λ₂) {M : Mom d → ℝ} {β : ℝ}
    (hβ : 0 ≤ β) (h : SNormR Λ₁ Λ₂ M ≤ ENNReal.ofReal β) : SNorm A W (cm M) ≤ ENNReal.ofReal β := by
  have hc : ContDiff ℝ Λ₁ (cm M) := VineEstS4c.contDiff_of_SNorm_le' hΛ (cm M) β h
  exact Induct.SNorm_mono_bound hA hW (cm M) hc β hβ h

end WaveTurbulence.VineEstS5C.P2
