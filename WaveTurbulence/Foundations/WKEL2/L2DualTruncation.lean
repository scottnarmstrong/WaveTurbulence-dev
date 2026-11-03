/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.UnweightedL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Bounded finite-support tests for nonnegative L² duality

The tested function may take the value infinity. Its tests are finite real
functions, and each test has genuine L² membership.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Cut off both the height and the spatial support of an extended nonnegative function. -/
@[expose] def dualTruncationNN (G : Mom d → ℝ≥0∞) (n : ℕ) : Mom d → ℝ≥0∞ :=
  (ball 0 ((n : ℝ) + 1)).indicator (fun k => min (G k) (ENNReal.ofReal ((n : ℝ) + 1)))

/-- The corresponding finite real L² test. -/
@[expose] def dualTruncation (G : Mom d → ℝ≥0∞) (n : ℕ) (k : Mom d) : ℝ :=
  (dualTruncationNN G n k).toReal

theorem measurable_dualTruncationNN {G : Mom d → ℝ≥0∞} (hG : Measurable G) (n : ℕ) :
    Measurable (dualTruncationNN G n) :=
  (hG.min measurable_const).indicator measurableSet_ball

theorem measurable_dualTruncation {G : Mom d → ℝ≥0∞} (hG : Measurable G) (n : ℕ) :
    Measurable (dualTruncation G n) := (measurable_dualTruncationNN hG n).ennreal_toReal

theorem dualTruncationNN_le_cap (G : Mom d → ℝ≥0∞) (n : ℕ) (k : Mom d) :
    dualTruncationNN G n k ≤ ENNReal.ofReal ((n : ℝ) + 1) := by
  by_cases hk : k ∈ ball 0 ((n : ℝ) + 1)
  · rw [dualTruncationNN, indicator_of_mem hk]
    exact min_le_right _ _
  · rw [dualTruncationNN, indicator_of_notMem hk]
    exact zero_le

theorem dualTruncationNN_le (G : Mom d → ℝ≥0∞) (n : ℕ) (k : Mom d) :
    dualTruncationNN G n k ≤ G k := by
  by_cases hk : k ∈ ball 0 ((n : ℝ) + 1)
  · rw [dualTruncationNN, indicator_of_mem hk]
    exact min_le_left _ _
  · rw [dualTruncationNN, indicator_of_notMem hk]
    exact zero_le

theorem dualTruncationNN_ne_top (G : Mom d → ℝ≥0∞) (n : ℕ) (k : Mom d) :
    dualTruncationNN G n k ≠ ⊤ :=
  ne_of_lt ((dualTruncationNN_le_cap G n k).trans_lt ENNReal.ofReal_lt_top)

theorem ofReal_dualTruncation (G : Mom d → ℝ≥0∞) (n : ℕ) (k : Mom d) :
    ENNReal.ofReal (dualTruncation G n k) = dualTruncationNN G n k :=
  ENNReal.ofReal_toReal (dualTruncationNN_ne_top G n k)

theorem dualTruncation_nonneg (G : Mom d → ℝ≥0∞) (n : ℕ) (k : Mom d) :
    0 ≤ dualTruncation G n k := ENNReal.toReal_nonneg

theorem dualTruncation_le_cap (G : Mom d → ℝ≥0∞) (n : ℕ) (k : Mom d) :
    dualTruncation G n k ≤ (n : ℝ) + 1 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (dualTruncationNN_le_cap G n k)
  simpa only [dualTruncation, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)] using h

/-- Each cutoff is a real Borel L² function on the full momentum space. -/
theorem memLp_dualTruncation {G : Mom d → ℝ≥0∞} (hG : Measurable G) (n : ℕ) :
    MemLp (dualTruncation G n) 2 := by
  have hi : MemLp ((ball (0 : Mom d) ((n : ℝ) + 1)).indicator (fun _ => (n : ℝ) + 1)) 2 :=
    memLp_indicator_const 2 measurableSet_ball.nullMeasurableSet _ (Or.inr measure_ball_lt_top.ne)
  refine hi.of_le (measurable_dualTruncation hG n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  by_cases hk : k ∈ ball (0 : Mom d) ((n : ℝ) + 1)
  · rw [indicator_of_mem hk, Real.norm_of_nonneg (dualTruncation_nonneg G n k),
      Real.norm_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)]
    exact dualTruncation_le_cap G n k
  · rw [indicator_of_notMem hk]
    simp only [dualTruncation, dualTruncationNN, indicator_of_notMem hk, ENNReal.toReal_zero, norm_zero]
    exact le_rfl

theorem dualTruncationNN_mono (G : Mom d → ℝ≥0∞) : Monotone (dualTruncationNN G) := by
  intro i j hij k
  by_cases hk : k ∈ ball (0 : Mom d) ((i : ℝ) + 1)
  · have hrad : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    have hk' : k ∈ ball (0 : Mom d) ((j : ℝ) + 1) := (ball_subset_ball hrad) hk
    rw [dualTruncationNN, indicator_of_mem hk, dualTruncationNN, indicator_of_mem hk']
    exact min_le_min_left _ (ENNReal.ofReal_le_ofReal hrad)
  · rw [dualTruncationNN, indicator_of_notMem hk]
    exact zero_le

/-- Increasing bounded finite-support cutoffs exhaust every extended value. -/
theorem iSup_dualTruncationNN (G : Mom d → ℝ≥0∞) (k : Mom d) :
    (⨆ n, dualTruncationNN G n k) = G k := by
  apply le_antisymm (iSup_le fun n => dualTruncationNN_le G n k)
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖k‖ (r : ℝ))
  have hnorm : ‖k‖ < (n : ℝ) + 1 := by
    have hm := le_max_left ‖k‖ (r : ℝ)
    linarith only [hm, hn]
  have hrR : (r : ℝ) ≤ (n : ℝ) + 1 := by
    have hm := le_max_right ‖k‖ (r : ℝ)
    linarith only [hm, hn]
  have hrNN : (r : ℝ≥0∞) ≤ ENNReal.ofReal ((n : ℝ) + 1) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hrR
  apply le_iSup_of_le n
  rw [dualTruncationNN, indicator_of_mem (mem_ball_zero_iff.mpr hnorm)]
  exact le_min hr.le hrNN

end WaveTurbulence.WKEL2
