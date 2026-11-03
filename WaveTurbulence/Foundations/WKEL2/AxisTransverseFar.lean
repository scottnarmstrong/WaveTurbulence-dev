/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.AxisKernel

/-!
# The far transverse part of the anisotropic kernel

Integrate the scalar coordinate first. The remaining power is `r^(1-2p)`,
which is integrable outside a ball exactly when `2p > n+1`.
-/

public section

noncomputable section

open MeasureTheory Set Metric

namespace WaveTurbulence.WKEL2

variable {n : ℕ}

/-- Slice integrability and mass at positive transverse radius. -/
theorem integrable_integral_axisKernel_slice (p : ℝ) (hp : 1 < p)
    (w : Mom n) (hw : 0 < ‖w‖) :
    Integrable (fun t : ℝ => axisKernel p (t, w)) ∧
      (∫ t : ℝ, axisKernel p (t, w)) = scalarSliceMass p * ‖w‖ ^ (1 - 2 * p) := by
  obtain ⟨hi, he⟩ := integrable_integral_scalarSlice p hp ‖w‖ hw
  refine ⟨?_, ?_⟩
  · change Integrable (fun t : ℝ => (t ^ 2 + ‖w‖ ^ 2) ^ (-p / 2) * ‖w‖ ^ (-p))
    exact hi.mul_const _
  · change (∫ t : ℝ, (t ^ 2 + ‖w‖ ^ 2) ^ (-p / 2) * ‖w‖ ^ (-p)) = _
    rw [integral_mul_const, he]
    calc
      _ = scalarSliceMass p * (‖w‖ ^ (1 - p) * ‖w‖ ^ (-p)) := by ring
      _ = _ := by rw [← Real.rpow_add hw, show 1 - p + -p = 1 - 2 * p by ring]

/-- Integrability on the region where the transverse radius is at least one. -/
theorem integrable_axisKernel_transverse_far (p : ℝ) (hp : 1 < p)
    (hdim : (n : ℝ) + 1 < 2 * p) :
    Integrable (fun z : ℝ × Mom n => if 1 ≤ ‖z.2‖ then axisKernel p z else 0)
      (volume.prod volume) := by
  let F : ℝ × Mom n → ℝ := fun z => if 1 ≤ ‖z.2‖ then axisKernel p z else 0
  have hm : Measurable F := (measurable_axisKernel p).piecewise
    (isClosed_le continuous_const continuous_snd.norm).measurableSet measurable_const
  refine (integrable_prod_iff' hm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun w => by
      by_cases hw : 1 ≤ ‖w‖
      · simpa only [F, hw, ↓reduceIte] using
          (integrable_integral_axisKernel_slice p hp w (zero_lt_one.trans_le hw)).1
      · simp only [F, hw, ↓reduceIte]
        exact integrable_zero _ _ _
  · have hb : (Module.finrank ℝ (Mom n) : ℝ) < 2 * p - 1 := by
      rw [finrank_euclideanSpace_fin]
      linarith only [hdim]
    have hi := ((integrableOn_exterior_norm_neg_rpow (volume : Measure (Mom n))
      (2 * p - 1) hb 1 zero_lt_one).integrable_indicator measurableSet_ball.compl).const_mul
        (scalarSliceMass p)
    apply hi.congr
    exact Filter.Eventually.of_forall fun w => by
      have hnorm : (fun t : ℝ => ‖F (t, w)‖) = fun t => F (t, w) := by
        funext t
        apply Real.norm_of_nonneg
        dsimp only [F]
        split_ifs
        · exact axisKernel_nonneg p (t, w)
        · exact le_refl 0
      dsimp only
      rw [hnorm]
      by_cases hw : 1 ≤ ‖w‖
      · have hmem : w ∈ (ball (0 : Mom n) 1)ᶜ := by
          simpa only [mem_compl_iff, mem_ball_zero_iff, not_lt] using hw
        simp only [F, hw, ↓reduceIte, indicator_of_mem hmem]
        rw [(integrable_integral_axisKernel_slice p hp w (zero_lt_one.trans_le hw)).2]
        congr 2
        ring
      · have hmem : w ∉ (ball (0 : Mom n) 1)ᶜ := by
          simpa only [mem_compl_iff, mem_ball_zero_iff, not_not] using (lt_of_not_ge hw)
        simp only [F, hw, ↓reduceIte, indicator_of_notMem hmem, mul_zero, integral_zero]

end WaveTurbulence.WKEL2
