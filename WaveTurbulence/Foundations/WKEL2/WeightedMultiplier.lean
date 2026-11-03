/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedL2

/-!
# Bounded multiplication in the frozen weighted L² norm
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Bounded Borel multipliers act on the genuine weighted L² space. -/
theorem weightedL2_mul_bounded (s : ℝ) {f q : Mom d → ℝ}
    (hf : MemLp (weightedFunction s f) 2) (hq : Measurable q)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ k, |q k| ≤ C) :
    MemLp (weightedFunction s (fun k => f k * q k)) 2 ∧
      weightedL2Norm s (fun k => f k * q k) ≤ C * weightedL2Norm s f := by
  let F := weightedFunction s f
  let H := weightedFunction s (fun k => f k * q k)
  have hH : AEStronglyMeasurable H volume := by
    have heq : H = fun k => F k * q k := by funext k; dsimp [H, F, weightedFunction]; ring
    rw [heq]
    exact hf.aestronglyMeasurable.mul hq.aestronglyMeasurable
  have hpoint (k : Mom d) : ‖H k‖ ≤ ‖C * F k‖ := by
    have heq : H k = F k * q k := by dsimp [H, F, weightedFunction]; ring
    rw [heq]
    simp only [norm_mul, Real.norm_of_nonneg hC]
    exact (mul_le_mul_of_nonneg_left (hb k) (norm_nonneg (F k))).trans_eq (mul_comm _ _)
  have hi : MemLp H 2 := (hf.const_mul C).of_le hH (Filter.Eventually.of_forall hpoint)
  refine ⟨hi, ?_⟩
  rw [weightedL2Norm_eq_norm_toLp s _ hi, weightedL2Norm_eq_norm_toLp s _ hf,
    Lp.norm_toLp, Lp.norm_toLp]
  have hmono := eLpNorm_mono_ae (p := (2 : ℝ≥0∞)) hH
    (Filter.Eventually.of_forall hpoint)
  have hreal := ENNReal.toReal_mono (hf.const_mul C).eLpNorm_ne_top hmono
  have heq : (hf.const_mul C).toLp (fun k => C * F k) = C • hf.toLp F := by
    apply Lp.ext
    filter_upwards [(hf.const_mul C).coeFn_toLp, hf.coeFn_toLp,
      Lp.coeFn_smul C (hf.toLp F)] with k hk hf' hsm
    rw [hk, hsm]
    change C * F k = C * (hf.toLp F) k
    rw [hf']
  have hnorm := congrArg norm heq
  rw [Lp.norm_toLp, norm_smul, Real.norm_of_nonneg hC, Lp.norm_toLp] at hnorm
  exact hreal.trans_eq hnorm

end WaveTurbulence.WKEL2
