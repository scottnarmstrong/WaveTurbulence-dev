/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.PhaseDifferences
import Mathlib.Tactic

/-!
# Adding arbitrary linear terms to an actual derivative tower

The shifted-lattice Poisson factor for a translated circle contributes a
linear dual phase. Its higher derivatives are unchanged, with no restriction
on the real translation parameter.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Actual derivative tower after adding `p*x+q` to its initial phase. -/
@[expose] def addLinearPhaseTower (F : ℕ → ℝ → ℝ) (p q : ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  F r x + if r = 0 then p*x+q else if r = 1 then p else 0

/-- Arbitrary linear terms preserve every derivative-tower relation. -/
theorem addLinearPhaseTower_hasDerivAt {F : ℕ → ℝ → ℝ} (p q : ℝ) (r : ℕ) (x : ℝ)
    (hd : HasDerivAt (F r) (F (r+1) x) x) :
    HasDerivAt (addLinearPhaseTower F p q r) (addLinearPhaseTower F p q (r+1) x) x := by
  by_cases h0 : r = 0
  · subst r
    have hp := (((hasDerivAt_id x).const_mul p).add_const q)
    simpa [addLinearPhaseTower] using! hd.add hp
  · by_cases h1 : r = 1
    · subst r
      have hf : addLinearPhaseTower F p q 1 = (fun y => F 1 y+p) := by
        funext y
        norm_num [addLinearPhaseTower]
      have hg : addLinearPhaseTower F p q (1+1) x = F 2 x := by
        norm_num [addLinearPhaseTower]
      rw [hf,hg]
      exact hd.add_const p
    · have hn0 : r+1 ≠ 0 := by omega
      have hn1 : r+1 ≠ 1 := by omega
      have hf : addLinearPhaseTower F p q r = F r := by
        funext y
        simp only [addLinearPhaseTower,ite_eq_right h0,ite_eq_right h1,add_zero]
      have hg : addLinearPhaseTower F p q (r+1) x = F (r+1) x := by
        simp only [addLinearPhaseTower,ite_eq_right hn0,ite_eq_right hn1,add_zero]
      rw [hf,hg]
      exact hd

/-- Every derivative of order at least two is unchanged. -/
theorem addLinearPhaseTower_of_two_le (F : ℕ → ℝ → ℝ) (p q : ℝ) {r : ℕ}
    (hr : 2 ≤ r) (x : ℝ) : addLinearPhaseTower F p q r x = F r x := by
  simp only [addLinearPhaseTower,ite_eq_right (show r ≠ 0 by omega),
    ite_eq_right (show r ≠ 1 by omega),add_zero]

end WaveTurbulence.NumberTheory
