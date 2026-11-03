/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.LinearSum

/-!
# The elementary time-window estimate

The first branch of TARGET `lemlin`, L1536–L1543. The argument works for
any nonnegative window length, before specializing to `δ L^(2γ)`.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Set

/-- The integrand of TARGET `lemlin` is continuous in time. -/
theorem continuous_norm_linear_flow {d : ℕ} {L : ℝ} (hL : 0 < L)
    (a r ξ : Mom d) : Continuous (fun s : ℝ => ‖linearLatticeSum L a (s • r + ξ)‖) :=
  ((continuous_linearLatticeSum hL a).comp (by fun_prop)).norm

/-- TARGET `lemlin`, elementary branch: a window of length `T` costs `L^d T`. -/
theorem integral_linear_flow_trivial {d : ℕ} {L T : ℝ} (hL : 1 ≤ L) (hT : 0 ≤ T)
    (a r ξ : Mom d) (τ : ℝ) :
    (∫ s in Icc τ (τ + T), ‖linearLatticeSum L a (s • r + ξ)‖) ≤
      (3 : ℝ) ^ d * L ^ d * T := by
  have hb := norm_setIntegral_le_of_norm_le_const_ae
    (μ := (volume : Measure ℝ)) (s := Icc τ (τ + T))
    (f := fun s => ‖linearLatticeSum L a (s • r + ξ)‖) isCompact_Icc.measure_lt_top
    (ae_of_all _ (fun s => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact norm_linearLatticeSum_le hL a _))
  rw [Real.norm_of_nonneg (integral_nonneg (fun s => norm_nonneg _))] at hb
  simpa only [Measure.real, Real.volume_Icc, add_sub_cancel_left,
    ENNReal.toReal_ofReal hT, mul_comm] using hb

end WaveTurbulence.LemLin
