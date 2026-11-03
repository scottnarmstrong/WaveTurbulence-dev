/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.NormPowerLocal
public import WaveTurbulence.Foundations.WKEL2.ScalarSlice
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The cylindrical anisotropic kernel

In coordinates `u = t θ + w`, the p-th power of the M₁ kernel is
`(t²+|w|²)^(-p/2) |w|^(-p)`.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {n : ℕ}

/-- Cylindrical form of the p-th power of the anisotropic kernel. -/
@[expose] def axisKernel (p : ℝ) (z : ℝ × Mom n) : ℝ :=
  (z.1 ^ 2 + ‖z.2‖ ^ 2) ^ (-p / 2) * ‖z.2‖ ^ (-p)

theorem axisKernel_nonneg (p : ℝ) (z : ℝ × Mom n) : 0 ≤ axisKernel p z :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem measurable_axisKernel (p : ℝ) : Measurable (axisKernel (n := n) p) :=
  (((measurable_fst.pow_const 2).add (measurable_snd.norm.pow_const 2)).pow_const (-p / 2)).mul
    (measurable_snd.norm.pow_const (-p))

/-- Geometric-mean bound used only on the bounded near field. -/
theorem axisKernel_one_le_product {z : ℝ × Mom n} (ht : z.1 ≠ 0) :
    axisKernel 1 z ≤ |z.1| ^ (-(1 : ℝ) / 2) * ‖z.2‖ ^ (-(3 : ℝ) / 2) := by
  by_cases hw : ‖z.2‖ = 0
  · simp only [axisKernel, hw, Real.zero_rpow (by norm_num : -(1 : ℝ) ≠ 0), mul_zero,
      Real.zero_rpow (by norm_num : -(3 : ℝ) / 2 ≠ 0)]
    exact le_refl 0
  · have hr : 0 < ‖z.2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    have ht0 : 0 < |z.1| := abs_pos.mpr ht
    have hs : |z.1| * ‖z.2‖ ≤ z.1 ^ 2 + ‖z.2‖ ^ 2 := by
      nlinarith only [sq_nonneg (|z.1| - ‖z.2‖), sq_abs z.1, sq_nonneg z.1,
        sq_nonneg ‖z.2‖]
    have h := Real.rpow_le_rpow_of_nonpos (mul_pos ht0 hr) hs
      (by norm_num : -(1 : ℝ) / 2 ≤ 0)
    rw [Real.mul_rpow ht0.le hr.le] at h
    have hm := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hr.le (-1))
    rw [mul_assoc, ← Real.rpow_add hr, show -(1 : ℝ) / 2 + -1 = -3 / 2 by norm_num] at hm
    exact hm

/-- Integrability of the anisotropic kernel on the bounded cylindrical near field. -/
theorem integrable_axisKernel_near (hn : 2 ≤ n) :
    Integrable ((ball (0 : ℝ × Mom n) 1).indicator (axisKernel 1)) (volume.prod volume) := by
  have hiT := (integrableOn_ball_norm_neg_rpow (volume : Measure ℝ)
    (by simp) (1 / 2) (by norm_num) 1).integrable_indicator measurableSet_ball
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hiW := (integrableOn_ball_norm_neg_rpow (volume : Measure (Mom n))
    (by rw [finrank_euclideanSpace_fin]; omega) (3 / 2)
    (by rw [finrank_euclideanSpace_fin]; linarith only [hnR]) 1).integrable_indicator measurableSet_ball
  have hi := hiT.mul_prod hiW
  have hnull : (volume.prod (volume : Measure (Mom n))) {z : ℝ × Mom n | z.1 = 0} = 0 := by
    have he : {z : ℝ × Mom n | z.1 = 0} = ({0} : Set ℝ) ×ˢ univ := by ext z; simp
    rw [he, Measure.prod_prod]
    simp only [measure_singleton, zero_mul]
  have hne : ∀ᵐ z : ℝ × Mom n ∂volume.prod volume, z.1 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  refine hi.mono' ((measurable_axisKernel 1).indicator measurableSet_ball).aestronglyMeasurable ?_
  filter_upwards [hne] with z hz
  rw [Real.norm_of_nonneg (indicator_nonneg (fun x _ => axisKernel_nonneg 1 x) z)]
  by_cases hball : z ∈ ball (0 : ℝ × Mom n) 1
  · have hzT : z.1 ∈ ball (0 : ℝ) 1 := by
      exact mem_ball_zero_iff.mpr ((norm_fst_le z).trans_lt (mem_ball_zero_iff.mp hball))
    have hzW : z.2 ∈ ball (0 : Mom n) 1 := by
      exact mem_ball_zero_iff.mpr ((norm_snd_le z).trans_lt (mem_ball_zero_iff.mp hball))
    simp only [indicator_of_mem hball, indicator_of_mem hzT, indicator_of_mem hzW,
      Real.norm_eq_abs]
    simpa only [neg_div] using axisKernel_one_le_product hz
  · rw [indicator_of_notMem hball]
    exact mul_nonneg (indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _)
      (indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _)

end WaveTurbulence.WKEL2
