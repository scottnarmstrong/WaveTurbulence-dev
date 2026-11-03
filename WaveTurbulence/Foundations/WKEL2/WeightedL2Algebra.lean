/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedL2Model

/-!
# Linear algebra in the exact weighted L² representation
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

theorem weightedFunction_add (s : ℝ) (f g : Mom d → ℝ) :
    weightedFunction s (f + g) = weightedFunction s f + weightedFunction s g := by
  funext k
  simp only [weightedFunction, Pi.add_apply, mul_add]

theorem weightedFunction_const_mul (s c : ℝ) (f : Mom d → ℝ) :
    weightedFunction s (fun k => c * f k) = fun k => c * weightedFunction s f k := by
  funext k
  dsimp only [weightedFunction]
  ring

theorem memLp_weighted_add (s : ℝ) {f g : Mom d → ℝ}
    (hf : MemLp (weightedFunction s f) 2) (hg : MemLp (weightedFunction s g) 2) :
    MemLp (weightedFunction s (f + g)) 2 := by
  rw [weightedFunction_add]
  exact hf.add hg

theorem memLp_weighted_const_mul (s c : ℝ) {f : Mom d → ℝ}
    (hf : MemLp (weightedFunction s f) 2) :
    MemLp (weightedFunction s (fun k => c * f k)) 2 := by
  rw [weightedFunction_const_mul]
  exact hf.const_mul c

/-- The frozen weighted norm satisfies Minkowski on its genuine domain. -/
theorem weightedL2Norm_add_le (s : ℝ) {f g : Mom d → ℝ}
    (hf : MemLp (weightedFunction s f) 2) (hg : MemLp (weightedFunction s g) 2) :
    weightedL2Norm s (f + g) ≤ weightedL2Norm s f + weightedL2Norm s g := by
  have hsum := memLp_weighted_add s (f := f) (g := g) hf hg
  rw [weightedL2Norm_eq_norm_toLp s (f + g) hsum, weightedL2Norm_eq_norm_toLp s f hf,
    weightedL2Norm_eq_norm_toLp s g hg, Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp]
  have hineq : eLpNorm (weightedFunction s (f + g)) 2 volume ≤
      eLpNorm (weightedFunction s f) 2 volume + eLpNorm (weightedFunction s g) 2 volume := by
    rw [weightedFunction_add]
    exact eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_lt_top.mpr ⟨hf.eLpNorm_lt_top, hg.eLpNorm_lt_top⟩).ne hineq
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] at hreal
  exact hreal

/-- Scalar multiplication is preserved by the weighted encoding. -/
theorem weightedL2Encode_const_mul (s c : ℝ) (f : Mom d → ℝ)
    (hf : MemLp (weightedFunction s f) 2) :
    weightedL2Encode s (fun k => c * f k) (memLp_weighted_const_mul s c (f := f) hf) =
      (c • weightedL2Encode s f hf : Lp ℝ 2 (volume : Measure (Mom d))) := by
  unfold weightedL2Encode
  have heq : weightedFunction s (fun k => c * f k) =ᵐ[volume] c • weightedFunction s f := by
    apply Filter.Eventually.of_forall
    intro k
    exact congrFun (weightedFunction_const_mul s c f) k
  exact (MemLp.toLp_congr (memLp_weighted_const_mul s c (f := f) hf) (hf.const_smul c) heq).trans
    (MemLp.toLp_const_smul c hf)

end WaveTurbulence.WKEL2
