/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.EndpointYoung
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Nonnegative convolution pairing by Tonelli and translation

This exact identity collapses two ordinary endpoint denominators before
the remaining two-variable Young inequality is applied. It includes
infinite values and assumes only measurability.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- Pairing against a sum is the same as pairing against the convolution. -/
theorem lintegral_add_pairing_eq_convolution (g h H : ℝ → ℝ≥0∞)
    (hg : Measurable g) (hh : Measurable h) (hH : Measurable H) (t : ℝ) :
    (∫⁻ y : ℝ, ∫⁻ z : ℝ, g y*h z*H (t+y+z)) =
      ∫⁻ w : ℝ, (∫⁻ y : ℝ, g y*h (w-y))*H (t+w) := by
  have hshift (y : ℝ) : (∫⁻ z : ℝ, g y*h z*H (t+y+z)) =
      ∫⁻ w : ℝ, g y*h (w-y)*H (t+w) := by
    rw [← lintegral_sub_right_eq_self (fun z : ℝ => g y*h z*H (t+y+z)) y]
    apply lintegral_congr
    intro w
    rw [show t+y+(w-y) = t+w by ring]
  simp_rw [hshift]
  have hm : Measurable (fun p : ℝ × ℝ => g p.1*h (p.2-p.1)*H (t+p.2)) :=
    ((hg.comp measurable_fst).mul (hh.comp (measurable_snd.sub measurable_fst))).mul
      (hH.comp (measurable_const.add measurable_snd))
  have hma : AEMeasurable (Function.uncurry (fun y w : ℝ => g y*h (w-y)*H (t+w)))
      (volume.prod volume) := hm.aemeasurable
  rw [lintegral_lintegral_swap hma]
  apply lintegral_congr
  intro w
  have hmw : AEMeasurable (fun y : ℝ => g y*h (w-y)) volume :=
    (hg.mul (hh.comp (measurable_const.sub measurable_id))).aemeasurable
  exact lintegral_mul_const'' (H (t+w)) hmw

end WaveTurbulence.SumintPar
