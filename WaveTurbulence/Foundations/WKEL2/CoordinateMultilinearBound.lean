/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedJets
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Coordinate bounds for multilinear operator norms
-/

public section

noncomputable section

namespace WaveTurbulence.WKEL2

variable {d n : ℕ}

/-- Scalar multilinear operator norms are controlled by the finite sum of coordinate components. -/
theorem norm_multilinear_le_coordinate_sum
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Mom d) ℝ) :
    ‖M‖ ≤ ∑ σ : Fin n → Fin d, |M (fun j => EuclideanSpace.single (σ j) (1 : ℝ))| := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  intro m
  have hm : m = fun j => ∑ i : Fin d, (m j) i • EuclideanSpace.single i (1 : ℝ) := by
    funext j
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (m j)]
    simp
  have Hexpand : M m = ∑ σ : Fin n → Fin d,
      (∏ j : Fin n, (m j) (σ j)) * M (fun j => EuclideanSpace.single (σ j) (1 : ℝ)) := by
    calc
      _ = M (fun j => ∑ i : Fin d, (m j) i • EuclideanSpace.single i (1 : ℝ)) := congrArg M hm
      _ = ∑ σ : Fin n → Fin d, M (fun j => (m j) (σ j) •
          EuclideanSpace.single (σ j) (1 : ℝ)) :=
        M.toMultilinearMap.map_sum (fun j (i : Fin d) => (m j) i • EuclideanSpace.single i (1 : ℝ))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro σ _
        simpa only [smul_eq_mul, ContinuousMultilinearMap.coe_coe] using M.toMultilinearMap.map_smul_univ
          (fun j => (m j) (σ j)) (fun j => EuclideanSpace.single (σ j) (1 : ℝ))
  calc
    ‖M m‖ = |∑ σ : Fin n → Fin d, (∏ j : Fin n, (m j) (σ j)) *
        M (fun j => EuclideanSpace.single (σ j) (1 : ℝ))| := by rw [Hexpand, Real.norm_eq_abs]
    _ ≤ ∑ σ : Fin n → Fin d, |(∏ j : Fin n, (m j) (σ j)) *
        M (fun j => EuclideanSpace.single (σ j) (1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : Fin n → Fin d, (∏ j : Fin n, ‖m j‖) *
        |M (fun j => EuclideanSpace.single (σ j) (1 : ℝ))| := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply Finset.prod_le_prod₀
      · intro j _
        exact abs_nonneg _
      · intro j _
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (m j) (σ j)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

/-- The Euclidean norm is bounded by the sum of absolute coordinates. -/
theorem norm_le_sum_abs_coordinates (k : Mom d) : ‖k‖ ≤ ∑ i : Fin d, |k i| := by
  have H : k = ∑ i : Fin d, k i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr k]
    simp
  conv_lhs => rw [H]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_smul]
  simp only [EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs, abs_one, mul_one]

end WaveTurbulence.WKEL2
