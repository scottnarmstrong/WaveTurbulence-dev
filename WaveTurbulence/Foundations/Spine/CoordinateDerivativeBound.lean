/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SNormOperations
public import Mathlib.Algebra.BigOperators.Ring.Finset
/-! From the source's coordinate-derivative norm to Fréchet-derivative bounds for smooth series. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

theorem norm_multilinear_le_coordinate_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d n : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Mom d) F) :
    ‖M‖ ≤ ∑ σ : Fin n → Fin d, ‖M (fun j => EuclideanSpace.single (σ j) (1 : ℝ))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (sum_nonneg fun _ _ => norm_nonneg _)
  intro m
  have hm : m = fun j => ∑ i : Fin d, (m j) i • EuclideanSpace.single i (1 : ℝ) := by
    funext j
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (m j)]
    simp
  have hexpand : M m = ∑ σ : Fin n → Fin d,
      (∏ j : Fin n, (m j) (σ j)) • M (fun j => EuclideanSpace.single (σ j) (1 : ℝ)) := by
    calc
      _ = M (fun j => ∑ i : Fin d, (m j) i • EuclideanSpace.single i (1 : ℝ)) := congrArg M hm
      _ = ∑ σ : Fin n → Fin d, M (fun j => (m j) (σ j) •
          EuclideanSpace.single (σ j) (1 : ℝ)) :=
        M.toMultilinearMap.map_sum (fun j (i : Fin d) => (m j) i • EuclideanSpace.single i (1 : ℝ))
      _ = _ := by
        apply sum_congr rfl
        intro σ _
        exact M.toMultilinearMap.map_smul_univ (fun j => (m j) (σ j))
          (fun j => EuclideanSpace.single (σ j) (1 : ℝ))
  rw [hexpand]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ σ : Fin n → Fin d, (∏ j : Fin n, ‖m j‖) *
        ‖M (fun j => EuclideanSpace.single (σ j) (1 : ℝ))‖ := by
      apply sum_le_sum
      intro σ _
      rw [norm_smul, Real.norm_eq_abs, abs_prod]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => ?_)
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (m j) (σ j)
    _ = _ := by rw [← mul_sum, mul_comm]

theorem SNorm_frechet_pointwise {d A B n : ℕ} (f : Mom d → ℂ) (hf : ContDiff ℝ A f)
    (C : ℝ) (hC : 0 ≤ C) (h : SNorm A B f ≤ ENNReal.ofReal C)
    (hn : n ≤ A) (x : Mom d) :
    jbr x ^ B * ‖iteratedFDeriv ℝ n f x‖ ≤ (d : ℝ) ^ n * C := by
  classical
  apply (mul_le_mul_of_nonneg_left (norm_multilinear_le_coordinate_sum
    (iteratedFDeriv ℝ n f x)) (pow_nonneg (Induct.jbr_pos x).le B)).trans
  rw [mul_sum]
  calc
    _ ≤ ∑ _σ : Fin n → Fin d, C := by
      apply sum_le_sum
      intro σ _
      exact Induct.SNorm_momentum_pointwise f hf C hC h hn σ x
    _ = _ := by simp

end WaveTurbulence.LGSpine
