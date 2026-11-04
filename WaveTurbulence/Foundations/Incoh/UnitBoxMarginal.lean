/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Marginals of a unit-box factorization

TARGET (incohproof18): after the root links are removed, the remaining
envelope is independent of the root times on their unit box. Tonelli then
bounds every root fiber by the full envelope integral.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- An exact unit-box factorization identifies the full integral and bounds each fiber. -/
theorem lintegral_fiber_le_of_unit_box_factorization {X Y : Type*}
    [MeasureSpace X] [MeasureSpace Y] [SigmaFinite (volume : Measure Y)]
    {B : Set X} (hB : MeasurableSet B) (hvol : volume B = 1)
    {G : X × Y → ℝ≥0∞} (hG : Measurable G) {H : Y → ℝ≥0∞}
    (hfactor : ∀ x y, G (x, y) = B.indicator (fun _ => H y) x) (x : X) :
    (∫⁻ y, G (x, y)) ≤ ∫⁻ z : X × Y, G z := by
  have hinner (x : X) : (∫⁻ y, G (x, y)) = B.indicator (fun _ => ∫⁻ y, H y) x := by
    by_cases hx : x ∈ B
    · simp_rw [hfactor, Set.indicator_of_mem (s := B) hx]
    · simp_rw [hfactor, Set.indicator_of_notMem (s := B) hx, lintegral_zero]
  have hfull : (∫⁻ z : X × Y, G z) = ∫⁻ y, H y := by
    change (∫⁻ z : X × Y, G z ∂((volume : Measure X).prod (volume : Measure Y))) = _
    rw [lintegral_prod G hG.aemeasurable]
    simp_rw [hinner]
    rw [lintegral_indicator_const hB, hvol, mul_one]
  rw [hfull, hinner]
  by_cases hx : x ∈ B
  · rw [Set.indicator_of_mem (s := B) hx]
  · rw [Set.indicator_of_notMem (s := B) hx]
    exact bot_le

end WaveTurbulence.Incoh
