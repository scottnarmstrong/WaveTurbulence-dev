/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzWeightedL2
public import WaveTurbulence.Foundations.WKEL2.UnweightedL2

/-!
# Monotonicity of the exact weighted Schwartz L² norms
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Increasing the exponent increases the pointwise absolute weighted value. -/
theorem abs_weightedFunction_mono {s t : ℝ} (hst : s ≤ t) (f : Mom d → ℝ) (k : Mom d) :
    |weightedFunction s f k| ≤ |weightedFunction t f k| := by
  simp only [weightedFunction, abs_mul]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) (s / 2)),
    abs_of_nonneg (Real.rpow_nonneg (by positivity) (t / 2))]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg ‖k‖))
      (div_le_div_of_nonneg_right hst (by norm_num))) (abs_nonneg _)

/-- Monotonicity uses the actual L² embeddings, so no integrability is inferred from a real norm. -/
theorem weightedL2Norm_mono_schwartz {s t : ℝ} (hst : s ≤ t) (f : 𝓢(Mom d, ℝ)) :
    weightedL2Norm s f ≤ weightedL2Norm t f := by
  rw [← norm_weightedToL2CLM, ← norm_weightedToL2CLM]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [weightedToL2CLM_coeFn s f, weightedToL2CLM_coeFn t f] with k hk₁ hk₂
  rw [hk₁, hk₂, Real.norm_eq_abs, Real.norm_eq_abs]
  exact abs_weightedFunction_mono hst f k

/-- A nonnegative frozen weight controls the unweighted squared energy. -/
theorem lintegral_norm_sq_le_weighted_schwartz (s : ℝ) (hs : 0 ≤ s) (f : 𝓢(Mom d, ℝ)) :
    (∫⁻ k, ENNReal.ofReal (‖f k‖ ^ 2)) ≤ ENNReal.ofReal (weightedL2Norm s f ^ 2) := by
  simp_rw [Real.norm_eq_abs, sq_abs]
  rw [lintegral_sq_eq_ofReal_weightedL2Norm_zero (f.memLp 2 volume)]
  exact ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (weightedL2Norm_nonneg _ _) (weightedL2Norm_mono_schwartz hs f) 2)

end WaveTurbulence.WKEL2
