/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Nonnegative two-region covers before time rescaling

A pointwise small/large cover on a finite box permits the inner domain
to be enlarged to the whole space. Joint measurability of the small
piece is enough for the two nonnegative masses to separate by Tonelli.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- A nonnegative small/large cover bounds the box mass by the two enlarged inner masses. -/
theorem lintegral_box_le_split {α : Type*} [MeasureSpace α] [SFinite (volume : Measure α)]
    (F A B : ℝ × α → ℝ≥0∞) (hA : Measurable A) (v w : ℝ) (S : Set α) (hS : MeasurableSet S)
    (hcover : ∀ t ∈ Icc v w, ∀ z ∈ S, F (t,z) ≤ A (t,z)+B (t,z)) :
    (∫⁻ t in Icc v w, ∫⁻ z in S, F (t,z)) ≤
      (∫⁻ t in Icc v w, ∫⁻ z : α, A (t,z))+
        (∫⁻ t in Icc v w, ∫⁻ z : α, B (t,z)) := by
  have hAi : Measurable (fun t : ℝ => ∫⁻ z : α, A (t,z)) := hA.lintegral_prod_right'
  calc
    _ ≤ ∫⁻ t in Icc v w, ∫⁻ z in S, A (t,z)+B (t,z) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hS] with z hz
      exact hcover t ht z hz
    _ ≤ ∫⁻ t in Icc v w, ∫⁻ z : α, A (t,z)+B (t,z) :=
      lintegral_mono (fun t => lintegral_mono' Measure.restrict_le_self le_rfl)
    _ = _ := by
      have he (t : ℝ) : (∫⁻ z : α, A (t,z)+B (t,z)) =
          (∫⁻ z : α, A (t,z))+(∫⁻ z : α, B (t,z)) :=
        lintegral_add_left (hA.comp ((measurable_const (a := t)).prodMk measurable_id)) _
      simp_rw [he]
      exact lintegral_add_left hAi _

end WaveTurbulence.Sumint
