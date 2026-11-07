/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.StripIntegral
import Mathlib.Tactic

/-!
# Fractional width gain for a strip inside a bounded time interval

For normal factors in dimension three, the first radial moment is
borderline. The interval length bound permits a square-root width gain,
which requires only a strictly integrable half moment.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- Bounded interval length converts a strip width to a half-power bound. -/
theorem min_three_width_le_sqrt {h x : ℝ} (hh : 0 ≤ h) (hx : 0 ≤ x) :
    min 3 (4*h+2*x) ≤ 8*(Real.sqrt h+Real.sqrt x) := by
  have hhs := Real.sqrt_nonneg h
  have hxs := Real.sqrt_nonneg x
  by_cases hs : 1 ≤ Real.sqrt h+Real.sqrt x
  · exact (min_le_left _ _).trans (by nlinarith only [hs])
  · have hh1 : Real.sqrt h ≤ 1 := by linarith only [hs,hxs]
    have hx1 : Real.sqrt x ≤ 1 := by linarith only [hs,hhs]
    have hh' : h ≤ Real.sqrt h := by
      nlinarith only [Real.sq_sqrt hh,mul_nonneg hhs (sub_nonneg.mpr hh1)]
    have hx' : x ≤ Real.sqrt x := by
      nlinarith only [Real.sq_sqrt hx,mul_nonneg hxs (sub_nonneg.mpr hx1)]
    exact (min_le_right _ _).trans (by nlinarith only [hh',hx',hhs,hxs])

/-- Tonelli and bounded interval length give the minimum of the interval and strip widths. -/
theorem lintegral_bounded_time_strip_le {α : Type*} [MeasureSpace α]
    [SFinite (volume : Measure α)] (f : α → ℝ≥0∞) (hf : Measurable f)
    (R : α → ℝ) (hR : Measurable R) (e v w : ℝ) (hlen : w-v ≤ 3) :
    (∫⁻ t in Icc v w, ∫⁻ z : α, if |t-e| ≤ R z then f z else 0) ≤
      ∫⁻ z : α, f z * ENNReal.ofReal (min 3 (2*R z)) := by
  have hm : Measurable (fun p : ℝ × α => if |p.1-e| ≤ R p.2 then f p.2 else 0) := by
    apply Measurable.ite
    · exact measurableSet_le (continuous_abs.measurable.comp
        (measurable_fst.sub (measurable_const (a := e)))) (hR.comp measurable_snd)
    · exact hf.comp measurable_snd
    · exact measurable_const
  have hma : AEMeasurable (Function.uncurry (fun t z => if |t-e| ≤ R z then f z else 0))
      ((volume.restrict (Icc v w)).prod volume) := hm.aemeasurable
  rw [lintegral_lintegral_swap hma]
  apply lintegral_mono
  intro z
  change (∫⁻ t in Icc v w, if |t-e| ≤ R z then f z else 0) ≤
    f z * ENNReal.ofReal (min 3 (2*R z))
  have he : (fun t : ℝ => if |t-e| ≤ R z then f z else 0) =
      (Icc (e-R z) (e+R z)).indicator (fun _ => f z) := by
    funext t
    have hh : |t-e| ≤ R z ↔ t ∈ Icc (e-R z) (e+R z) := by
      rw [abs_le,mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith only [h.1,h.2]
    simp only [hh,indicator_apply]
  rw [he,lintegral_indicator measurableSet_Icc,lintegral_const,
    Measure.restrict_apply_univ,Measure.restrict_apply measurableSet_Icc]
  have h0 : volume (Icc (e-R z) (e+R z) ∩ Icc v w) ≤ ENNReal.ofReal 3 := by
    calc
      _ ≤ volume (Icc v w) := measure_mono inter_subset_right
      _ = ENNReal.ofReal (w-v) := Real.volume_Icc
      _ ≤ _ := ENNReal.ofReal_le_ofReal hlen
  have h1 : volume (Icc (e-R z) (e+R z) ∩ Icc v w) ≤ ENNReal.ofReal (2*R z) := by
    calc
      _ ≤ volume (Icc (e-R z) (e+R z)) := measure_mono inter_subset_left
      _ = _ := by rw [Real.volume_Icc]; congr 1; ring
  exact mul_le_mul' le_rfl (by simpa only [ENNReal.ofReal_min] using le_min h0 h1)

end WaveTurbulence.SumintPar
