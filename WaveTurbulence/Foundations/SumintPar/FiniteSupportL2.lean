/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-!
# L² control of a bounded amplitude on at most nine units of volume

At most two selected input coordinates each range over an interval of
length at most three. The numerical factor three is their square-root
volume bound. This generic lemma makes no source trace-estimate claim.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- A measurable amplitude bounded by B and supported on volume at most nine has L² norm at most 3B. -/
theorem eLpNorm_two_le_three_mul_of_support {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ) {s : Set α} (hs : MeasurableSet s)
    (hvol : μ s ≤ ENNReal.ofReal 9) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ s, ‖f x‖ ≤ B) (hzero : ∀ x ∉ s, f x = 0) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (3*B) := by
  let g := s.indicator (fun _ : α => (B:ℂ))
  have hfg : ∀ x, ‖f x‖ ≤ ‖g x‖ := by
    intro x
    by_cases hx : x ∈ s
    · dsimp [g]
      rw [Set.indicator_of_mem hx,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
      exact hbound x hx
    · dsimp [g]
      rw [hzero x hx,Set.indicator_of_notMem hx,norm_zero]
  have hc : ‖(B:ℂ)‖ₑ = ENNReal.ofReal B := by
    rw [← ofReal_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
  have hg : eLpNorm g 2 μ = ENNReal.ofReal B*(μ s)^((1:ℝ)/2) := by
    rw [eLpNorm_indicator_const hs.nullMeasurableSet (by norm_num) (by norm_num),hc]
    norm_num
  have hv : (μ s)^((1:ℝ)/2) ≤ ENNReal.ofReal 3 := by
    calc
      _ ≤ (ENNReal.ofReal 9)^((1:ℝ)/2) := ENNReal.rpow_le_rpow hvol (by norm_num)
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 9)]
        congr 1
        rw [← Real.sqrt_eq_rpow]
        norm_num
  calc
    _ ≤ eLpNorm g 2 μ := eLpNorm_mono_ae hf (ae_of_all _ hfg)
    _ = ENNReal.ofReal B*(μ s)^((1:ℝ)/2) := hg
    _ ≤ ENNReal.ofReal B*ENNReal.ofReal 3 := mul_le_mul' le_rfl hv
    _ = _ := by rw [← ENNReal.ofReal_mul hB]; congr 1; ring

/-- The same bounded-support amplitude belongs to L². -/
theorem memLp_two_of_support_volume_le_nine {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ) {s : Set α} (hs : MeasurableSet s)
    (hvol : μ s ≤ ENNReal.ofReal 9) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ s, ‖f x‖ ≤ B) (hzero : ∀ x ∉ s, f x = 0) : MemLp f 2 μ :=
  (eLpNorm_two_le_three_mul_of_support hf hs hvol hB hbound hzero).trans_lt ENNReal.ofReal_lt_top

end WaveTurbulence.SumintPar
