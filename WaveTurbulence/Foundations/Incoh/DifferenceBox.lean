/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Difference-coordinate densities for time boxes

TARGET (incohproof14)–(incohproof15). Tonelli identifies the density in
the time difference. A separating time gives the extra first moment.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The fiber of the time difference `y-x=r` through a product box. -/
@[expose] def differenceFiber (I J : Set ℝ) (r : ℝ) : Set ℝ :=
  {x | x ∈ I ∧ x + r ∈ J}

theorem measurableSet_differenceFiber {I J : Set ℝ} (hI : MeasurableSet I)
    (hJ : MeasurableSet J) (r : ℝ) : MeasurableSet (differenceFiber I J r) :=
  hI.inter (hJ.preimage (measurable_id.add_const r))

/-- Every fiber has at most the mass of its first interval. -/
theorem volume_differenceFiber_le (I J : Set ℝ) (r : ℝ) :
    volume (differenceFiber I J r) ≤ volume I :=
  measure_mono fun _ hx => hx.1

/-- A separating time bounds the fiber density by the absolute time difference. -/
theorem volume_differenceFiber_le_abs {I J : Set ℝ} {q : ℝ}
    (hsep : (∀ x ∈ I, x ≤ q) ∧ (∀ y ∈ J, q ≤ y)) (r : ℝ) :
    volume (differenceFiber I J r) ≤ ENNReal.ofReal |r| := by
  calc
    _ ≤ volume (Icc (q - |r|) q) := by
      apply measure_mono
      intro x hx
      have hxq := hsep.1 x hx.1
      have hqy := hsep.2 (x + r) hx.2
      exact ⟨by linarith [le_abs_self r], hxq⟩
    _ = _ := by rw [Real.volume_Icc]; congr 1; ring

/-- The time-box integral disintegrates against the exact difference-fiber density. -/
theorem lintegral_difference_box {I J : Set ℝ} (hI : MeasurableSet I)
    (hJ : MeasurableSet J) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : ℝ × ℝ, (I ×ˢ J).indicator (fun z => f (z.2 - z.1)) z) =
      ∫⁻ r : ℝ, f r * volume (differenceFiber I J r) := by
  let H : ℝ × ℝ → ℝ≥0∞ := (I ×ˢ J).indicator (fun z => f (z.2 - z.1))
  have hH : Measurable H := (hf.comp (measurable_snd.sub measurable_fst)).indicator (hI.prod hJ)
  have hs := (measurePreserving_prod_add (volume : Measure ℝ) (volume : Measure ℝ)).lintegral_comp hH
  change (∫⁻ z : ℝ × ℝ, H z ∂(volume.prod volume)) = _
  rw [← hs]
  have heq : (fun z : ℝ × ℝ => H (z.1, z.1 + z.2)) =
      fun z => (differenceFiber I J z.2).indicator (fun _ => f z.2) z.1 := by
    funext z
    dsimp only [H]
    by_cases hz : z.1 ∈ I ∧ z.1 + z.2 ∈ J
    · rw [Set.indicator_of_mem (s := I ×ˢ J) (a := (z.1, z.1 + z.2)) hz,
        Set.indicator_of_mem (s := differenceFiber I J z.2) (a := z.1) hz]
      rw [add_sub_cancel_left]
    · rw [Set.indicator_of_notMem (s := I ×ˢ J) (a := (z.1, z.1 + z.2)) hz,
        Set.indicator_of_notMem (s := differenceFiber I J z.2) (a := z.1) hz]
  have hG : Measurable (fun z : ℝ × ℝ =>
      (differenceFiber I J z.2).indicator (fun _ => f z.2) z.1) := by
    rw [← heq]
    exact hH.comp (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  rw [heq, lintegral_prod_symm _ hG.aemeasurable]
  apply lintegral_congr
  intro r
  change (∫⁻ x, (differenceFiber I J r).indicator (fun _ => f r) x) = _
  rw [lintegral_indicator_const (measurableSet_differenceFiber hI hJ r)]

/-- The zeroth-moment bound for any product box with first side of measure at most one. -/
theorem lintegral_difference_box_le {I J : Set ℝ} (hI : MeasurableSet I)
    (hJ : MeasurableSet J) (hvol : volume I ≤ 1) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : ℝ × ℝ, (I ×ˢ J).indicator (fun z => f (z.2 - z.1)) z) ≤ ∫⁻ r, f r := by
  rw [lintegral_difference_box hI hJ hf]
  apply lintegral_mono
  intro r
  simpa only [mul_one] using
    mul_le_mul' (le_refl (f r)) ((volume_differenceFiber_le I J r).trans hvol)

/-- TARGET (incohproof15): a separating time replaces the zeroth moment by the first moment. -/
theorem lintegral_difference_box_le_firstMoment {I J : Set ℝ} (hI : MeasurableSet I)
    (hJ : MeasurableSet J) {q : ℝ}
    (hsep : (∀ x ∈ I, x ≤ q) ∧ (∀ y ∈ J, q ≤ y))
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : ℝ × ℝ, (I ×ˢ J).indicator (fun z => f (z.2 - z.1)) z) ≤
      ∫⁻ r, f r * ENNReal.ofReal |r| := by
  rw [lintegral_difference_box hI hJ hf]
  exact lintegral_mono fun r => mul_le_mul' le_rfl (volume_differenceFiber_le_abs hsep r)

end WaveTurbulence.Incoh
