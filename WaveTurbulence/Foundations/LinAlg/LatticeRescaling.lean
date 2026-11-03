/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LinAlg.LatticeObservations

/-!
# Lattice rescaling estimates

Elementary rescaling and Euclidean bounds for TARGET Lemma A.6.
-/

public section

namespace WaveTurbulence.LinAlg
open Finset
open scoped Classical InnerProductSpace Pointwise

/-- Lattice rescaling is scalar multiplication on momentum space. -/
theorem latticePoint_eq_inv_smul {d : ℕ} (L : ℝ) (n : Fin d → ℤ) :
    latticePoint L n = L⁻¹ • latticePoint 1 n := by
  apply WithLp.ofLp_injective
  funext i
  simp [latticePoint, div_eq_mul_inv, mul_comm]

/-- Invert the lattice rescaling when `L` is nonzero. -/
theorem latticePoint_one_eq_smul {d : ℕ} {L : ℝ} (hL : L ≠ 0) (n : Fin d → ℤ) :
    latticePoint 1 n = L • latticePoint L n := by
  rw [latticePoint_eq_inv_smul L n, smul_smul, mul_inv_cancel₀ hL, one_smul]

/-- Rescaling the lattice preserves the span of any family. -/
theorem span_latticePoint_eq {ι : Type*} {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    (v : ι → Fin d → ℤ) :
    Submodule.span ℝ (Set.range fun i => latticePoint L (v i)) =
      Submodule.span ℝ (Set.range fun i => latticePoint 1 (v i)) := by
  simp_rw [latticePoint_eq_inv_smul L]
  rw [Set.range_smul]
  exact Submodule.span_smul_eq_of_isUnit _ _ (isUnit_iff_ne_zero.mpr (inv_ne_zero hL))

/-- Euclidean norm is bounded by the sum of the absolute coordinates. -/
theorem norm_mom_le_sum_abs {d : ℕ} (x : Mom d) : ‖x‖ ≤ ∑ i, |x i| := by
  have h := sum_sq_le_sq_sum_of_nonneg (s := (univ : Finset (Fin d)))
    (fun i _ => abs_nonneg (x i))
  simp only [sq_abs, ← EuclideanSpace.real_norm_sq_eq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h

/-- Rescaling decreases the norm for `L ≥ 1`. -/
theorem norm_latticePoint_le_one {d : ℕ} {L : ℝ} (hL : 1 ≤ L) (n : Fin d → ℤ) :
    ‖latticePoint L n‖ ≤ ‖latticePoint 1 n‖ := by
  rw [latticePoint_eq_inv_smul L n, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (by linarith : 0 < L)]
  exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hL)

/-- Convert a source norm bound into an integer-coordinate norm bound. -/
theorem norm_latticePoint_one_le {d : ℕ} {L M : ℝ} (hL : 0 < L) (n : Fin d → ℤ)
    (hn : ‖latticePoint L n‖ ≤ M) : ‖latticePoint 1 n‖ ≤ L * M := by
  rw [latticePoint_one_eq_smul hL.ne', norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left hn hL.le

/-- Convert a source inner-product bound into an integer-coordinate bound. -/
theorem abs_inner_latticePoint_one_le {d : ℕ} {L M : ℝ} (hL : 0 < L)
    (k z : Fin d → ℤ) (hz : |⟪latticePoint L k, latticePoint L z⟫_ℝ| ≤ M) :
    |⟪latticePoint 1 k, latticePoint 1 z⟫_ℝ| ≤ L ^ 2 * M := by
  rw [inner_latticePoint, abs_div, abs_of_pos (sq_pos_of_pos hL)] at hz
  rw [inner_latticePoint, one_pow, div_one]
  simpa only [mul_comm] using (div_le_iff₀ (sq_pos_of_pos hL)).mp hz

end WaveTurbulence.LinAlg
