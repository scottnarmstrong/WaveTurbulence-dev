/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Expanding the square of a nonnegative parameter integral
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- Tonelli expansion of a weighted square, with infinite values allowed. -/
theorem lintegral_weighted_square {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {W : α → ℝ≥0∞} {H : α × β → ℝ≥0∞} (hW : Measurable W) (hH : Measurable H) :
    (∫⁻ x, W x * (∫⁻ y, H (x, y) ∂ν) ^ 2 ∂μ) =
      ∫⁻ p : β × β, ∫⁻ x, W x * H (x, p.1) * H (x, p.2) ∂μ ∂ν.prod ν := by
  have hJoint : Measurable (fun p : α × (β × β) => W p.1 * H (p.1, p.2.1) * H (p.1, p.2.2)) :=
    ((hW.comp measurable_fst).mul
      (hH.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).mul
        (hH.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  calc
    _ = ∫⁻ x, ∫⁻ p : β × β, W x * H (x, p.1) * H (x, p.2) ∂ν.prod ν ∂μ := by
      apply lintegral_congr
      intro x
      have hx : Measurable (fun y : β => H (x, y)) :=
        hH.comp (measurable_const.prodMk measurable_id)
      have hp : Measurable (fun p : β × β => H (x, p.1) * H (x, p.2)) :=
        (hx.comp measurable_fst).mul (hx.comp measurable_snd)
      rw [pow_two, ← lintegral_prod_mul hx.aemeasurable hx.aemeasurable,
        ← lintegral_const_mul _ hp]
      apply lintegral_congr
      intro p
      exact (mul_assoc _ _ _).symm
    _ = _ := lintegral_lintegral_swap hJoint.aemeasurable

end WaveTurbulence.WKEL2
