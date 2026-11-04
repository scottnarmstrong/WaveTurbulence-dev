/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Frozen.Defs.Mom
import Mathlib.Tactic

/-!
# Coordinate bounds control the multilinear derivative norm

Expanding every vector in the coordinate basis gives the crude factor
`d^n`. Here `n ≤ 30d`, so this factor depends only on dimension and is
sufficient for localized Fourier-L1 estimates in sumint Step 1.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- Exact reconstruction from the standard Euclidean coordinates. -/
theorem sum_coordinates_single {d : ℕ} (x : Mom d) :
    (∑ j : Fin d, x j • EuclideanSpace.single j (1 : ℝ)) = x := by
  ext i
  simp [Pi.single_apply]

/-- Bounding a multilinear map on all coordinate basis words bounds its operator norm. -/
theorem multilinear_norm_le_of_coordinate_bounds {d n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Mom d) ℂ)
    {B : ℝ} (hB : 0 ≤ B)
    (hT : ∀ ρ : Fin n → Fin d, ‖T (fun i => EuclideanSpace.single (ρ i) 1)‖ ≤ B) :
    ‖T‖ ≤ (d : ℝ) ^ n * B := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hB)
  intro v
  have he : T v = ∑ ρ : Fin n → Fin d,
      (∏ i, v i (ρ i)) • T (fun i => EuclideanSpace.single (ρ i) 1) := by
    conv_lhs => rw [show v = fun i => ∑ j : Fin d, v i j • EuclideanSpace.single j (1 : ℝ) by
      funext i; exact (sum_coordinates_single (v i)).symm]
    have hs : (T fun i => ∑ j : Fin d, v i j • EuclideanSpace.single j (1 : ℝ)) =
        ∑ ρ : Fin n → Fin d, T (fun i => v i (ρ i) • EuclideanSpace.single (ρ i) (1 : ℝ)) :=
      T.toMultilinearMap.map_sum (fun i j => v i j • EuclideanSpace.single j (1 : ℝ))
    rw [hs]
    apply Finset.sum_congr rfl
    intro ρ _
    exact T.toMultilinearMap.map_smul_univ _ _
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ρ : Fin n → Fin d, B * ∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro ρ _
      rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
      have hp : (∏ i : Fin n, |v i (ρ i)|) ≤ ∏ i, ‖v i‖ := by
        apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro i _
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v i) (ρ i)
      exact (mul_le_mul hp (hT ρ) (norm_nonneg _) (by positivity)).trans_eq (by ring)
    _ = _ := by simp [mul_assoc, mul_comm, mul_left_comm]

end WaveTurbulence.Sumint
