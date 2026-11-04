/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Time-strip measures in the sumint factor estimates

Ordering and interval incoherence restrict one time variable to a strip
near an endpoint. The estimates retain both the unit-interval bound and
the strip-width bound, including the enlarged intervals of Step 3.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- A radius-R strip around an endpoint is contained in its literal closed interval. -/
theorem strip_subset_interval (e R : ℝ) : {u : ℝ | |u-e| ≤ R} ⊆ Icc (e-R) (e+R) := by
  intro u hu
  change |u-e| ≤ R at hu
  have h := abs_le.mp hu
  constructor <;> linarith only [h.1, h.2]

/-- Intersecting a unit interval with a time strip costs at most either available length. -/
theorem volume_unit_strip_le (q e : ℝ) {R : ℝ} :
    volume (Icc q (q+1) ∩ {u : ℝ | |u-e| ≤ R}) ≤
      min 1 (ENNReal.ofReal (2*R)) := by
  apply le_min
  · calc
      _ ≤ volume (Icc q (q+1)) := measure_mono Set.inter_subset_left
      _ = 1 := by rw [Real.volume_Icc]; norm_num
  · calc
      _ ≤ volume (Icc (e-R) (e+R)) :=
        measure_mono (Set.inter_subset_right.trans (strip_subset_interval e R))
      _ = _ := by rw [Real.volume_Icc]; congr 1; ring

/-- The same bound with the exact enlarged-unit-interval length. -/
theorem volume_enlarged_unit_strip_le (q e : ℝ) {R h : ℝ} :
    volume (Icc (q-h) (q+1+h) ∩ {u : ℝ | |u-e| ≤ R}) ≤
      min (ENNReal.ofReal (1+2*h)) (ENNReal.ofReal (2*R)) := by
  apply le_min
  · calc
      _ ≤ volume (Icc (q-h) (q+1+h)) := measure_mono Set.inter_subset_left
      _ = _ := by rw [Real.volume_Icc]; congr 1; ring
  · calc
      _ ≤ volume (Icc (e-R) (e+R)) :=
        measure_mono (Set.inter_subset_right.trans (strip_subset_interval e R))
      _ = _ := by rw [Real.volume_Icc]; congr 1; ring

end WaveTurbulence.Sumint
