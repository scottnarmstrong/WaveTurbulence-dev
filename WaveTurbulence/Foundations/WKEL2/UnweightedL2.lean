/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedL2

/-!
# The zero-weight case of the frozen L² norm
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

theorem weightedFunction_zero (f : Mom d → ℝ) : weightedFunction 0 f = f := by
  funext k
  simp only [weightedFunction, zero_div, Real.rpow_zero, one_mul]

/-- The zero-weight frozen norm has the usual nonnegative squared integral. -/
theorem lintegral_sq_eq_ofReal_weightedL2Norm_zero {f : Mom d → ℝ} (hf : MemLp f 2) :
    (∫⁻ k, ENNReal.ofReal ((f k) ^ 2)) = ENNReal.ofReal ((weightedL2Norm 0 f) ^ 2) := by
  have hi : MemLp (weightedFunction 0 f) 2 := by rw [weightedFunction_zero]; exact hf
  simpa only [weightedFunction_zero] using (ofReal_weightedL2Norm_sq 0 f hi).symm

/-- Removing a weight already absorbed into the function leaves the frozen norm unchanged. -/
theorem weightedL2Norm_zero_weightedFunction (s : ℝ) (f : Mom d → ℝ) :
    weightedL2Norm 0 (weightedFunction s f) = weightedL2Norm s f := by
  change Real.sqrt (∫ k, (weightedFunction 0 (weightedFunction s f) k) ^ 2) =
    Real.sqrt (∫ k, (weightedFunction s f k) ^ 2)
  rw [weightedFunction_zero]

end WaveTurbulence.WKEL2
