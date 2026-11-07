/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Nonnegative affine time rescaling

The ordering-strip arguments discard rectangular restrictions before
rescaling an inner time. Nonnegative integrals allow this without any
prior absolute-integrability premise on the oscillatory majorants.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory ENNReal

namespace WaveTurbulence.SumintPar

/-- Positive scalar rescaling of a nonnegative real-time integral. -/
theorem lintegral_comp_mul_pos (f : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    (∫⁻ s : ℝ, f (c*s)) = ENNReal.ofReal c⁻¹ * ∫⁻ s : ℝ, f s := by
  have he := lintegral_map_equiv (μ := (volume : Measure ℝ)) f (Homeomorph.mulLeft₀ c hc.ne').toMeasurableEquiv
  change (∫⁻ s : ℝ, f s ∂Measure.map (fun s => c*s) volume) =
    ∫⁻ s : ℝ, f (c*s) at he
  rw [← he,Real.map_volume_mul_left hc.ne',lintegral_smul_measure,
    abs_of_pos (inv_pos.mpr hc),smul_eq_mul]

/-- Positive affine rescaling of a nonnegative real-time integral. -/
theorem lintegral_comp_affine_pos (f : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (∫⁻ s : ℝ, f (c*(s-t))) = ENNReal.ofReal c⁻¹ * ∫⁻ s : ℝ, f s := by
  have he : (fun s : ℝ => f (c*(s-t))) = fun s => (fun u => f (c*u)) (s+(-t)) := by
    funext s
    rw [sub_eq_add_neg]
  rw [he]
  calc
    _ = ∫⁻ s : ℝ, f (c*s) := lintegral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun u => f (c*u)) (-t)
    _ = _ := lintegral_comp_mul_pos f hc

/-- Two independent affine time changes have exactly the reciprocal-square scale. -/
theorem lintegral_comp_affine_two_pos (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f)
    {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (∫⁻ s : ℝ, ∫⁻ s' : ℝ, f (c*(s-t),c*(s'-t))) =
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal c⁻¹ * ∫⁻ z : ℝ × ℝ, f z := by
  have he (s : ℝ) := lintegral_comp_affine_pos (fun u => f (c*(s-t),u)) hc t
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_affine_pos (fun v => ∫⁻ w : ℝ, f (v,w)) hc t]
  rw [Measure.volume_eq_prod,lintegral_prod _ hf.aemeasurable]
  rw [mul_assoc]

end WaveTurbulence.SumintPar
