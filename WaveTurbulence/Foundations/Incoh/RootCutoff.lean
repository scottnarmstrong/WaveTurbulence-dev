/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.Chi0
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The fixed cutoff for local root clocks

TARGET (incohproof19). Dilate the landed cutoff by two: it is smooth,
compactly supported, and exactly one on the entire unit root interval.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- The fixed root-clock cutoff, one on `[-1,1]` and supported in `[-2,2]`. -/
@[expose] def rootCutoff (t : ℝ) : ℝ := Fourier.chi0 (t / 2)

@[fun_prop] theorem contDiff_rootCutoff : ContDiff ℝ ∞ rootCutoff :=
  Fourier.chi0_contDiff.comp (by fun_prop)

theorem hasCompactSupport_rootCutoff : HasCompactSupport rootCutoff := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2))
  intro t ht
  apply Fourier.chi0_eq_zero
  by_contra h
  have hh : |t / 2| < 1 := lt_of_not_ge h
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  have ha : |t| < 2 := by linarith
  exact ht (abs_le.mp ha.le)

theorem rootCutoff_eq_one {t : ℝ} (ht : |t| ≤ 1) : rootCutoff t = 1 := by
  apply Fourier.chi0_eq_one
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right ht (by norm_num)

end WaveTurbulence.Incoh
