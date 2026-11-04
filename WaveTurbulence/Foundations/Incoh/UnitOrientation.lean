/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Int.Associated
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Unit orientations preserve the frequency moments

TARGET (incohproof10), (incohproof14)–(incohproof15): the branching
orientation is an integer unit, so changing its sign costs no constant.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Integer-unit multiplication preserves the zeroth frequency moment. -/
theorem lintegral_intUnit_mul (u : ℤˣ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ s : ℝ, f (((u : ℤ) : ℝ) * s)) = ∫⁻ s : ℝ, f s := by
  rcases Int.units_eq_one_or u with hu | hu
  · simp only [hu, Units.val_one, Int.cast_one, one_mul]
  · simp only [hu, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
    exact lintegral_neg_eq_self (μ := (volume : Measure ℝ)) f

/-- Integer-unit multiplication preserves the first absolute frequency moment. -/
theorem lintegral_firstMoment_intUnit_mul (u : ℤˣ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ s : ℝ, f (((u : ℤ) : ℝ) * s) * ENNReal.ofReal |s|) =
      ∫⁻ s : ℝ, f s * ENNReal.ofReal |s| := by
  rcases Int.units_eq_one_or u with hu | hu
  · simp only [hu, Units.val_one, Int.cast_one, one_mul]
  · simp only [hu, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
    have h := lintegral_neg_eq_self (μ := (volume : Measure ℝ)) (fun s : ℝ => f s * ENNReal.ofReal |s|)
    simpa only [abs_neg] using h

end WaveTurbulence.Incoh
