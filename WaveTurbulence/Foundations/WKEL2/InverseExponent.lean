/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.ConjExponents
import Mathlib.Tactic

/-!
# Conjugate exponents for the inverse-norm convolution
-/

public section

namespace WaveTurbulence.WKEL2

/-- In spatial dimension `n`, inverse-norm convolution with `⟨x⟩⁻ᵃ` admits
Hölder exponents precisely in the open range `a > n-1`. -/
theorem exists_inverse_holder_exponents (n : ℕ) (hn : 2 ≤ n) (a : ℝ)
    (ha : (n : ℝ) - 1 < a) :
    ∃ p q : ℝ, p.HolderConjugate q ∧ (n : ℝ) < p ∧ (n : ℝ) < a * q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - 1 := by linarith only [hnR]
  have ha0 : 0 < a := hden.trans ha
  have hnum : 0 < (n : ℝ) := by linarith only [hnR]
  have h1 : 1 < (n : ℝ) / (n - 1) := (lt_div_iff₀ hden).mpr (by linarith)
  have h2 : (n : ℝ) / a < (n : ℝ) / (n - 1) :=
    div_lt_div_of_pos_left hnum hden ha
  obtain ⟨q, hq, hqu⟩ := exists_between (max_lt h1 h2)
  have hq1 : 1 < q := (le_max_left _ _).trans_lt hq
  have hqa : (n : ℝ) / a < q := (le_max_right _ _).trans_lt hq
  refine ⟨q / (q - 1), q, (Real.HolderConjugate.conjExponent hq1).symm, ?_, ?_⟩
  · apply (lt_div_iff₀ (sub_pos.mpr hq1)).mpr
    have h := (lt_div_iff₀ hden).mp hqu
    nlinarith only [h]
  · have h := (div_lt_iff₀ ha0).mp hqa
    exact h.trans_eq (mul_comm _ _)

end WaveTurbulence.WKEL2
