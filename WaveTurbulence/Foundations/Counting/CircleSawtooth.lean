/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleArc
public import WaveTurbulence.Foundations.NumberTheory.SmoothingBounds
import Mathlib.Tactic

/-!
# Sawtooth sums on translated circular height blocks

Quantitative ingredients for NT-CIRCLE-v2 goal 2. The square-root frequency
bound used in the smoothing inequality is proved here for the actual circle
height. Only geometric height-block assumptions remain. No global circle
discrepancy statement is claimed by these local estimates.
-/

public section

namespace WaveTurbulence.Counting

/-- Square-root frequency growth for the actual translated circular phase. -/
theorem circle_arc_exp_sum_le_sqrt {R c t d H : ℝ} {a b : ℕ}
    (hab : a ≤ b) (hR : 0 < R) (hH : 0 < H)
    (hblock : ∀ x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1),
      circleHeight R c (x + t) ∈ Set.Icc H (2 * H))
    {n : ℕ} (hn : 0 < n) :
    ‖∑ k ∈ Finset.Ioc a b,
      NumberTheory.expPhase ((n : ℝ) * (circleHeight R c ((k : ℝ) + t) + d))‖ ≤
      (8 * (8 * ((b : ℝ) - a) * Real.sqrt (R ^ 2 / (8 * H ^ 3)) +
        1 / Real.sqrt (R ^ 2 / (8 * H ^ 3)))) * Real.sqrt n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlam : 0 < R ^ 2 / (8 * H ^ 3) := by positivity
  have hs : 0 < Real.sqrt (R ^ 2 / (8 * H ^ 3)) := Real.sqrt_pos.mpr hlam
  have hsn : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hmul : Real.sqrt (R ^ 2 / (8 * H ^ 3)) ≤
      Real.sqrt n * Real.sqrt (R ^ 2 / (8 * H ^ 3)) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsn hs.le
  have hinv : 1 / (Real.sqrt n * Real.sqrt (R ^ 2 / (8 * H ^ 3))) ≤
      Real.sqrt n / Real.sqrt (R ^ 2 / (8 * H ^ 3)) :=
    (one_div_le_one_div_of_le hs hmul).trans (div_le_div_of_nonneg_right hsn hs.le)
  have h := circle_arc_exp_sum_le (d := (n : ℝ) * d) hab hR hH hnR hblock
  rw [Real.sqrt_mul hnR.le] at h
  have heq : (∑ k ∈ Finset.Ioc a b,
      NumberTheory.expPhase ((n : ℝ) * (circleHeight R c ((k : ℝ) + t) + d))) =
      ∑ k ∈ Finset.Ioc a b,
        NumberTheory.expPhase ((n : ℝ) * circleHeight R c ((k : ℝ) + t) + (n : ℝ) * d) := by
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    ring
  rw [heq]
  calc
    _ ≤ 8 * (8 * ((b : ℝ) - a) *
        (Real.sqrt n * Real.sqrt (R ^ 2 / (8 * H ^ 3))) +
        1 / (Real.sqrt n * Real.sqrt (R ^ 2 / (8 * H ^ 3)))) := h
    _ ≤ 8 * (8 * ((b : ℝ) - a) *
        (Real.sqrt n * Real.sqrt (R ^ 2 / (8 * H ^ 3))) +
        Real.sqrt n / Real.sqrt (R ^ 2 / (8 * H ^ 3))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hinv) (by norm_num)
    _ = _ := by ring

/-- The local circular sawtooth estimate, with arbitrary smoothing cutoff `K`.
Every frequency bound required by the Fourier inequality is discharged by
`circle_arc_exp_sum_le_sqrt`. -/
theorem circle_arc_sawtooth_sum_le {R c t d H : ℝ} {a b K : ℕ}
    (hab : a ≤ b) (hR : 0 < R) (hH : 0 < H) (hK : 0 < K)
    (hblock : ∀ x ∈ Set.Icc ((a : ℝ) + 1) ((b : ℝ) + 1),
      circleHeight R c (x + t) ∈ Set.Icc H (2 * H)) :
    |∑ k ∈ Finset.Ioc a b, NumberTheory.sawtooth (circleHeight R c ((k : ℝ) + t) + d)| ≤
      ((b : ℝ) - a) / (2 * K) + ((2 * Real.pi + 2) / Real.pi ^ 2) *
        (8 * (8 * ((b : ℝ) - a) * Real.sqrt (R ^ 2 / (8 * H ^ 3)) +
          1 / Real.sqrt (R ^ 2 / (8 * H ^ 3)))) * Real.sqrt K := by
  have hN : (0 : ℝ) ≤ (b : ℝ) - a := by
    apply sub_nonneg.mpr
    exact_mod_cast hab
  have hA : 0 ≤ 8 * (8 * ((b : ℝ) - a) * Real.sqrt (R ^ 2 / (8 * H ^ 3)) +
      1 / Real.sqrt (R ^ 2 / (8 * H ^ 3))) := by positivity
  have h := NumberTheory.abs_sum_sawtooth_le_of_sqrt_exp_sum (Finset.Ioc a b)
    (fun k : ℕ => circleHeight R c ((k : ℝ) + t) + d) hA hK
    (fun n hn => circle_arc_exp_sum_le_sqrt hab hR hH hblock hn)
  have hc : ((Finset.Ioc a b).card : ℝ) = (b : ℝ) - a := by
    rw [Nat.card_Ioc, Nat.cast_sub hab]
  rw [hc] at h
  exact h

end WaveTurbulence.Counting
