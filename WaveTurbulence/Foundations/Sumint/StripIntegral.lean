/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.StripMeasure
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Exact integration of variable-width time strips

Tonelli turns an ordering or incoherence strip into its literal width.
No integrability premise is needed before the nonnegative majorant is
integrated. The statement also covers empty strips.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- Integrating a variable-width strip costs exactly its width. -/
theorem lintegral_time_strip (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (R : ℝ → ℝ) (hR : Measurable R) (e : ℝ) :
    (∫⁻ t : ℝ, ∫⁻ s : ℝ, if |t-e| ≤ R s then f s else 0) =
      ∫⁻ s : ℝ, f s * ENNReal.ofReal (2*R s) := by
  have hm : Measurable (fun p : ℝ × ℝ => if |p.1-e| ≤ R p.2 then f p.2 else 0) := by
    apply Measurable.ite
    · exact measurableSet_le (continuous_abs.measurable.comp (measurable_fst.sub (measurable_const (a := e))))
        (hR.comp measurable_snd)
    · exact hf.comp measurable_snd
    · exact measurable_const
  have hma : AEMeasurable (Function.uncurry (fun t s : ℝ =>
      if |t-e| ≤ R s then f s else 0)) (volume.prod volume) := hm.aemeasurable
  rw [lintegral_lintegral_swap hma]
  apply lintegral_congr
  intro s
  have he : (fun t : ℝ => if |t-e| ≤ R s then f s else 0) =
      (Icc (e-R s) (e+R s)).indicator (fun _ => f s) := by
    funext t
    have hh : |t-e| ≤ R s ↔ t ∈ Icc (e-R s) (e+R s) := by
      rw [abs_le, mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith only [h.1,h.2]
    simp only [hh, indicator_apply]
  rw [he, lintegral_indicator measurableSet_Icc, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Icc]
  congr 2
  ring

end WaveTurbulence.Sumint
