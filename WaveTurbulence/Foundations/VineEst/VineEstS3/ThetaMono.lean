/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # Monotonicity of `XNorm`, `XNormRestr` in the time weight `θ` (V5, row bounds from `η` to `6η⁶`) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3
open WaveTurbulence MeasureTheory
open scoped ENNReal

theorem maxBracketPow_mono {r : ℕ} {θ θ' : ℝ} (h : θ ≤ θ') (lam : Fin r → ℝ) :
    maxBracketPow θ lam ≤ maxBracketPow θ' lam := by
  unfold maxBracketPow
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_exponent_le le_sup_right h

theorem XNorm_mono_theta {r d : ℕ} {θ θ' : ℝ} (h : θ ≤ θ') (Λ₁ Λ₂ : ℕ) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ Λ₁ Λ₂ F ≤ XNorm θ' Λ₁ Λ₂ F := by
  classical
  unfold XNorm
  split_ifs with hc
  · refine iSup₂_mono fun ρ hρ => ?_
    refine lintegral_mono fun lam => ?_
    exact mul_le_mul_left (maxBracketPow_mono h lam) _
  · exact le_rfl

theorem XNormRestr_mono_theta {r d : ℕ} {θ θ' : ℝ} (h : θ ≤ θ') (Λ₁ Λ₂ : ℕ) (B : Set (Fin r → ℝ))
    (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNormRestr θ Λ₁ Λ₂ B K F ≤ XNormRestr θ' Λ₁ Λ₂ B K F := by
  unfold XNormRestr
  refine le_iInf₂ fun G hG => ?_
  exact (iInf₂_le G hG).trans (XNorm_mono_theta h _ _ G)

end WaveTurbulence.VineEstS3
