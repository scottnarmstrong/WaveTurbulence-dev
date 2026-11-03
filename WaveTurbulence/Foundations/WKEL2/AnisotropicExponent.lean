/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.Exponents
public import Mathlib.Basic.Real.ConjExponents

/-!
# Conjugate exponents for the anisotropic convolution
-/

public section

namespace WaveTurbulence.WKEL2

/-- The M₁ Hölder window, expressed directly in terms of the two conjugate exponents. -/
theorem exists_anisotropic_holder_exponents (d : ℕ) (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ p q : ℝ, p.HolderConjugate q ∧ (d : ℝ) < 2 * p ∧
      p < (d : ℝ) - 1 ∧ (d : ℝ) < (2 * s) * q := by
  obtain ⟨q, hqdecay, hqlo, hqhi⟩ := exists_holder_exponent_M1 d hd s hs
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 2 := by linarith only [hdR]
  have hs0 : 0 < 2 * s := by linarith only [hs, hdR]
  have hq1 : 1 < q := by
    have h : 1 < (d - 1 : ℝ) / (d - 2) :=
      (lt_div_iff₀ hden).mpr (by linarith)
    exact h.trans hqlo
  have hqden : 0 < q - 1 := sub_pos.mpr hq1
  refine ⟨q / (q - 1), q, (Real.HolderConjugate.conjExponent hq1).symm, ?_, ?_, ?_⟩
  · rw [← mul_div_assoc]
    apply (lt_div_iff₀ hqden).mpr
    have h := (lt_div_iff₀ hden).mp hqhi
    nlinarith only [h]
  · apply (div_lt_iff₀ hqden).mpr
    have h := (div_lt_iff₀ hden).mp hqlo
    nlinarith only [h]
  · have h := (div_lt_iff₀ hs0).mp hqdecay
    exact h.trans_eq (mul_comm _ _)

end WaveTurbulence.WKEL2
