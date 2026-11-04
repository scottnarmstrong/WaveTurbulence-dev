/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import WaveTurbulence.Foundations.Analysis.SmoothCutoffPacket

/-!
# A fixed cutoff for the unit time interval

A bump equal to one on the radius-two ball and supported in the
radius-three ball supplies a single cutoff and hence universal constants.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Analysis

/-- The fixed real bump underlying the unit-time cutoff. -/
@[expose] def unitTimeBump : ContDiffBump (0 : ℝ) where
  rIn := 2
  rOut := 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Complex-valued smooth compactly supported cutoff, equal to one on `[0,1]`. -/
@[expose] noncomputable def unitTimeCutoff (t : ℝ) : ℂ := unitTimeBump t

theorem contDiff_unitTimeCutoff : ContDiff ℝ ∞ unitTimeCutoff :=
  Complex.ofRealCLM.contDiff.comp unitTimeBump.contDiff

theorem hasCompactSupport_unitTimeCutoff : HasCompactSupport unitTimeCutoff := by
  exact unitTimeBump.hasCompactSupport.comp_left rfl

theorem unitTimeCutoff_eq_one {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : unitTimeCutoff t = 1 := by
  have hm : t ∈ Metric.closedBall (0 : ℝ) unitTimeBump.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans (by norm_num [unitTimeBump])
  change (unitTimeBump t : ℂ) = 1
  rw [unitTimeBump.one_of_mem_closedBall hm, Complex.ofReal_one]

end WaveTurbulence.Analysis
