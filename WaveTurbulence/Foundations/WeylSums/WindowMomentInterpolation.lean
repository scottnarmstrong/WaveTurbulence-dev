/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.FiniteMeasureInterpolation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Moment interpolation on symmetric time windows -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

theorem volume_abs_window (T : ℝ) : volume {t : ℝ | |t| ≤ T} = ENNReal.ofReal (2*T) := by
  have heq : {t : ℝ | |t| ≤ T} = Icc (-T) T := by
    ext t
    change |t| ≤ T ↔ -T ≤ t ∧ t ≤ T
    exact abs_le
  rw [heq,Real.volume_Icc]
  congr 1
  ring

/-- Interpolation between two positive moment orders on a finite window. -/
theorem window_moment_interpolation (f : ℝ → ℝ) (hf : Measurable f)
    (hfn : ∀ t, 0 ≤ f t) (a b T : ℝ) (hb : 0 < b) (hba : b < a) (hT : 0 ≤ T)
    (hi : IntegrableOn (fun t => f t^a) {t : ℝ | |t| ≤ T}) :
    IntegrableOn (fun t => f t^b) {t : ℝ | |t| ≤ T} ∧
      (∫ t in {t : ℝ | |t| ≤ T}, f t^b) ≤
        (∫ t in {t : ℝ | |t| ≤ T}, f t^a)^(b/a)*(2*T)^(1-b/a) := by
  have ha : 0 < a := hb.trans hba
  have hθ : b/a ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hb ha,(div_lt_one ha).mpr hba⟩
  have hmass : (volume.restrict {t : ℝ | |t| ≤ T}) univ ≤ ENNReal.ofReal (2*T) := by
    rw [Measure.restrict_apply_univ,volume_abs_window]
  have hh := integral_small_power_le (volume.restrict {t : ℝ | |t| ≤ T})
    (fun t => f t^a) (hf.pow_const a) (fun t => Real.rpow_nonneg (hfn t) _) hi (b/a) (2*T) hθ (by positivity) hmass
  have hpow (t : ℝ) : (f t^a)^(b/a) = f t^b := by
    rw [← Real.rpow_mul (hfn t)]
    congr 1
    field_simp
  simpa only [hpow,IntegrableOn] using hh

end WaveTurbulence.WeylSums
