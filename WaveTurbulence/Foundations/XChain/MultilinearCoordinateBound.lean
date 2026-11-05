/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SNormOperations
public import Mathlib.Analysis.Calculus.SmoothSeries
/-! Coordinate bounds control the operator norms required by the smooth-series theorem. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem euclidean_sum_coordinates {d : ℕ} (x : Mom d) :
    x = ∑ j, x j • EuclideanSpace.single j (1 : ℝ) := by
  ext k
  simp [Pi.single_apply]

theorem multilinear_norm_le_coordinate_bound {d n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Mom d) ℂ)
    (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ ρ : Fin n → Fin d, ‖T (fun i => EuclideanSpace.single (ρ i) 1)‖ ≤ M) :
    ‖T‖ ≤ (d : ℝ) ^ n * M := by
  classical
  apply T.opNorm_le_bound (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) n) hM)
  intro v
  have hexp : T v = ∑ ρ : Fin n → Fin d,
      (∏ i, v i (ρ i)) • T (fun i => EuclideanSpace.single (ρ i) 1) := by
    have hvec : v = fun i => ∑ j, v i j • EuclideanSpace.single j (1 : ℝ) := by
      funext i
      exact euclidean_sum_coordinates (v i)
    conv_lhs => rw [hvec]
    have hmap := T.toMultilinearMap.map_sum (fun (i : Fin n) (j : Fin d) =>
      v i j • EuclideanSpace.single j (1 : ℝ))
    apply hmap.trans
    apply sum_congr rfl
    intro ρ _
    exact T.map_smul_univ _ _
  rw [hexp]
  calc
    _ ≤ ∑ ρ : Fin n → Fin d, (∏ i, ‖v i‖) * M := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro ρ _
      rw [norm_smul, Real.norm_eq_abs, abs_prod]
      exact mul_le_mul (prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v i) (ρ i)))
        (h ρ) (norm_nonneg _) (prod_nonneg (fun i _ => norm_nonneg _))
    _ = ((d : ℝ) ^ n * M) * ∏ i, ‖v i‖ := by
      rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

end WaveTurbulence.Induct
