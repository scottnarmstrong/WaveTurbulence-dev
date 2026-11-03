/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.CubicFrequency

/-!
# A uniform first-frequency-moment recurrence

The exact integration-by-parts formula costs one power of the stationary
scale and keeps all amplitudes inside the fixed compact class.
-/

public section

namespace WaveTurbulence.LemLin
open Finset
open scoped Classical

/-- Multiplication by one frequency coordinate costs at most one scale factor. -/
theorem scalarCubic_frequency_le (kind : CubicPhase) (f : Fin 3 → ScalarCutoff)
    (s t : ℝ) (j : Fin 3) (ν : Fin 3 → ℝ) :
    |ν j| * ‖scalarCubicIntegral kind f s t ν‖ ≤
      ‖scalarCubicIntegral kind (Function.update f j (f j).differentiate) s t ν‖ +
        (4 * Real.pi * cubicScale s t) *
          ∑ k, ‖scalarCubicIntegral kind (Function.update f k (f k).mulCoordinate) s t ν‖ := by
  let M (k : Fin 3) : ℂ := scalarCubicIntegral kind (Function.update f k (f k).mulCoordinate) s t ν
  let D : ℂ := scalarCubicIntegral kind (Function.update f j (f j).differentiate) s t ν
  have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hS : ‖∑ k, (cubicMatrix kind s t j k : ℂ) * M k‖ ≤
      (2 * cubicScale s t) * ∑ k, ‖M k‖ := by
    calc
      _ ≤ ∑ k, ‖(cubicMatrix kind s t j k : ℂ) * M k‖ := norm_sum_le _ _
      _ ≤ ∑ k, (2 * cubicScale s t) * ‖M k‖ := by
        apply sum_le_sum
        intro k _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_cubicMatrix_le kind s t j k) (norm_nonneg _)
      _ = _ := (mul_sum _ _ _).symm
  have he : (2 * Real.pi) * (|ν j| * ‖scalarCubicIntegral kind f s t ν‖) =
      ‖D + (2 * Real.pi * Complex.I) * ∑ k, (cubicMatrix kind s t j k : ℂ) * M k‖ := by
    have hn := congrArg norm (scalarCubic_frequency_identity kind f s t j ν)
    rw [norm_mul, norm_neg, norm_mul, hc, Complex.norm_real, Real.norm_eq_abs] at hn
    simpa only [mul_assoc] using hn
  have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc
    _ ≤ (2 * Real.pi) * (|ν j| * ‖scalarCubicIntegral kind f s t ν‖) :=
      le_mul_of_one_le_left (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hp
    _ = _ := he
    _ ≤ ‖D‖ + ‖(2 * Real.pi * Complex.I) * ∑ k, (cubicMatrix kind s t j k : ℂ) * M k‖ :=
      norm_add_le _ _
    _ ≤ ‖D‖ + (2 * Real.pi) * ((2 * cubicScale s t) * ∑ k, ‖M k‖) := by
      rw [norm_mul, hc]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hS (by positivity))
    _ = _ := by ring

end WaveTurbulence.LemLin
