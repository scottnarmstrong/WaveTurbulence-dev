/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedL2Algebra

/-!
# Negation, subtraction, and almost everywhere equality in the frozen weighted norm
-/

public section

noncomputable section

open MeasureTheory

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

theorem weightedFunction_neg (s : ℝ) (f : Mom d → ℝ) :
    weightedFunction s (-f) = -weightedFunction s f := by
  funext k
  simp only [weightedFunction, Pi.neg_apply, mul_neg]

theorem weightedFunction_sub (s : ℝ) (f g : Mom d → ℝ) :
    weightedFunction s (f - g) = weightedFunction s f - weightedFunction s g := by
  rw [sub_eq_add_neg, weightedFunction_add, weightedFunction_neg, sub_eq_add_neg]

theorem memLp_weighted_neg (s : ℝ) {f : Mom d → ℝ} (hf : MemLp (weightedFunction s f) 2) :
    MemLp (weightedFunction s (-f)) 2 := by
  rw [weightedFunction_neg]
  exact hf.neg

theorem memLp_weighted_sub (s : ℝ) {f g : Mom d → ℝ}
    (hf : MemLp (weightedFunction s f) 2) (hg : MemLp (weightedFunction s g) 2) :
    MemLp (weightedFunction s (f - g)) 2 := by
  rw [weightedFunction_sub]
  exact hf.sub hg

theorem weightedL2Norm_neg (s : ℝ) (f : Mom d → ℝ) :
    weightedL2Norm s (-f) = weightedL2Norm s f := by
  unfold weightedL2Norm
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun k => by
    simp only [Pi.neg_apply, mul_neg, neg_sq]

theorem weightedL2Norm_sub_le (s : ℝ) {f g : Mom d → ℝ}
    (hf : MemLp (weightedFunction s f) 2) (hg : MemLp (weightedFunction s g) 2) :
    weightedL2Norm s (f - g) ≤ weightedL2Norm s f + weightedL2Norm s g := by
  rw [sub_eq_add_neg]
  have h := weightedL2Norm_add_le s (f := f) (g := -g) hf (memLp_weighted_neg s hg)
  simpa only [weightedL2Norm_neg] using h

/-- The frozen norm depends only on the almost everywhere class of its input. -/
theorem weightedL2Norm_congr_ae (s : ℝ) {f g : Mom d → ℝ} (hfg : f =ᵐ[volume] g) :
    weightedL2Norm s f = weightedL2Norm s g := by
  unfold weightedL2Norm
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with k hk
  rw [hk]

theorem memLp_weighted_congr_ae (s : ℝ) {f g : Mom d → ℝ}
    (hf : MemLp (weightedFunction s f) 2) (hfg : f =ᵐ[volume] g) :
    MemLp (weightedFunction s g) 2 := by
  refine MemLp.ae_eq (hfg.mono fun k hk => ?_) hf
  exact congrArg (fun r : ℝ => (1 + ‖k‖ ^ 2) ^ (s / 2) * r) hk

end WaveTurbulence.WKEL2
