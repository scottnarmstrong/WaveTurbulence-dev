/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantSymmetry
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Reflection invariances of the resonant integral

These are the changes of variables used in the gain Schur test.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Measure-level nonnegative swap formula. -/
theorem lintegral_resonantMeasure_swap {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {F : Mom d × Mom d → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F (p.2, p.1) ∂resonantMeasure e) = ∫⁻ p, F p ∂resonantMeasure e := by
  have h := lintegral_map (μ := resonantMeasure e) hF measurable_swap
  rw [map_swap_resonantMeasure he hd] at h
  simpa only [Prod.swap] using h.symm

/-- Reflection of the transverse variable preserves resonant integration. -/
theorem lintegral_resonantMeasure_neg_second (e : Mom d)
    {F : Mom d × Mom d → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F (p.1, -p.2) ∂resonantMeasure e) = ∫⁻ p, F p ∂resonantMeasure e := by
  have hneg : Measurable (fun p : Mom d × Mom d => F (p.1, -p.2)) :=
    hF.comp (measurable_fst.prodMk measurable_snd.neg)
  rw [lintegral_resonantMeasure_chart e hneg, lintegral_resonantMeasure_chart e hF]
  apply lintegral_congr
  intro a
  apply congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal (‖a‖⁻¹) * z)
  have h := lintegral_neg_eq_self (μ := (volume : Measure ↥(ℝ ∙ e)ᗮ))
    (fun w : ↥(ℝ ∙ e)ᗮ => F (a, normalReflection e a w))
  simpa only [Submodule.coe_neg, map_neg] using h

/-- Reflection of the first normal preserves resonant integration. -/
theorem lintegral_resonantMeasure_neg_first {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {F : Mom d × Mom d → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F (-p.1, p.2) ∂resonantMeasure e) = ∫⁻ p, F p ∂resonantMeasure e := by
  have hneg : Measurable (fun p : Mom d × Mom d => F (-p.1, p.2)) :=
    hF.comp (measurable_fst.neg.prodMk measurable_snd)
  have hsw : Measurable (fun p : Mom d × Mom d => F (p.2, p.1)) := hF.comp measurable_swap
  calc
    _ = ∫⁻ p, F (-p.2, p.1) ∂resonantMeasure e :=
      (lintegral_resonantMeasure_swap he hd hneg).symm
    _ = ∫⁻ p, F (p.2, p.1) ∂resonantMeasure e :=
      lintegral_resonantMeasure_neg_second e hsw
    _ = _ := lintegral_resonantMeasure_swap he hd hF

end WaveTurbulence.WKEL2
