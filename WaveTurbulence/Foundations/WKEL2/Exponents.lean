/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!+# Hölder exponent windows

The two open exponent windows in Lemma 4 of
`docs/research/git20-general-d.md`, valid throughout the sharp open range.
-/

public section

namespace WaveTurbulence.WKEL2

/-- The conjugate exponent window for the hyperplane kernel `M₂`.
Here `q` is the exponent denoted `p'` in the research note. -/
theorem exists_holder_exponent_M2 (d : ℕ) (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ q : ℝ, 1 < q ∧ (d - 1 : ℝ) / (2 * s) < q ∧
      q < (d - 1 : ℝ) / (d - 2) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 2 := by linarith only [hdR]
  have hnum : 0 < (d : ℝ) - 1 := by linarith only [hdR]
  have hsd : (d : ℝ) - 2 < 2 * s := by linarith only [hs]
  have h1 : 1 < (d - 1 : ℝ) / (d - 2) :=
    (lt_div_iff₀ hden).mpr (by linarith)
  have h2 : (d - 1 : ℝ) / (2 * s) < (d - 1 : ℝ) / (d - 2) :=
    div_lt_div_of_pos_left hnum hden hsd
  obtain ⟨q, hq, hqu⟩ := exists_between (max_lt h1 h2)
  exact ⟨q, (le_max_left _ _).trans_lt hq,
    (le_max_right _ _).trans_lt hq, hqu⟩

/-- The conjugate exponent window for the codimension-two angular kernel `M₁`.
The lower and upper bounds correspond to `d/2 < p < d-1`. -/
theorem exists_holder_exponent_M1 (d : ℕ) (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ q : ℝ, (d : ℝ) / (2 * s) < q ∧
      (d - 1 : ℝ) / (d - 2) < q ∧ q < (d : ℝ) / (d - 2) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 2 := by linarith only [hdR]
  have hnum : 0 < (d : ℝ) := by linarith only [hdR]
  have hsd : (d : ℝ) - 2 < 2 * s := by linarith only [hs]
  have h1 : (d : ℝ) / (2 * s) < (d : ℝ) / (d - 2) :=
    div_lt_div_of_pos_left hnum hden hsd
  have h2 : (d - 1 : ℝ) / (d - 2) < (d : ℝ) / (d - 2) :=
    div_lt_div_of_pos_right (by linarith) hden
  obtain ⟨q, hq, hqu⟩ := exists_between (max_lt h1 h2)
  exact ⟨q, (le_max_left _ _).trans_lt hq, (le_max_right _ _).trans_lt hq, hqu⟩

end WaveTurbulence.WKEL2
