/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Tactic

/-!
# A denominator-free orthogonal residual

Cramer's rule clears the denominators in orthogonal projection. This is the
integer-preserving Gram–Schmidt step used in TARGET Lemma A.6.
-/

public section

namespace WaveTurbulence.LinAlg
open Finset Module
open scoped Classical InnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

/-- The orthogonal residual multiplied by the Gram determinant. -/
@[expose] noncomputable def gramResidual (w : ι → E) (u : E) : E :=
  (Matrix.gram ℝ w).det • u -
    ∑ i, (Matrix.gram ℝ w).cramer (fun j => ⟪w j, u⟫_ℝ) i • w i

/-- The denominator-free residual is orthogonal to every input vector. -/
theorem inner_gramResidual (w : ι → E) (u : E) (i : ι) :
    ⟪w i, gramResidual w u⟫_ℝ = 0 := by
  have heq := congrFun ((Matrix.gram ℝ w).mulVec_cramer (fun j => ⟪w j, u⟫_ℝ)) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.gram_apply] at heq
  simp only [gramResidual, inner_sub_right, inner_smul_right, inner_sum]
  rw [show (∑ x, (Matrix.gram ℝ w).cramer (fun j => ⟪w j, u⟫_ℝ) x * ⟪w i, w x⟫_ℝ) =
      (Matrix.gram ℝ w).det * ⟪w i, u⟫_ℝ by simpa only [mul_comm] using heq]
  exact sub_self _

/-- The residual remains in the span after adjoining the new vector. -/
theorem gramResidual_mem_span (w : ι → E) (u : E) :
    gramResidual w u ∈ Submodule.span ℝ (insert u (Set.range w)) := by
  apply Submodule.sub_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩))

/-- A new direction produces a nonzero residual when the old vectors are independent. -/
theorem gramResidual_ne_zero {w : ι → E} {u : E} (hw : LinearIndependent ℝ w)
    (hu : u ∉ Submodule.span ℝ (Set.range w)) : gramResidual w u ≠ 0 := by
  have hd : (Matrix.gram ℝ w).det ≠ 0 :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hw
  intro hz
  have heq : (Matrix.gram ℝ w).det • u =
      ∑ i, (Matrix.gram ℝ w).cramer (fun j => ⟪w j, u⟫_ℝ) i • w i :=
    sub_eq_zero.mp hz
  have hm : (Matrix.gram ℝ w).det • u ∈ Submodule.span ℝ (Set.range w) := by
    rw [heq]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact hu ((Submodule.smul_mem_iff _ hd).mp hm)

/-- The Gram determinant is bounded by the elementary determinant estimate. -/
theorem abs_det_gram_le {w : ι → E} {B : ℝ} (hB : 0 ≤ B) (hw : ∀ i, ‖w i‖ ≤ B) :
    |(Matrix.gram ℝ w).det| ≤ (Fintype.card ι).factorial * B ^ (2 * Fintype.card ι) := by
  have hentry (i j : ι) : |(Matrix.gram ℝ w) i j| ≤ B ^ 2 := by
    exact (abs_real_inner_le_norm _ _).trans (by simpa only [pow_two] using (mul_le_mul (hw i) (hw j) (norm_nonneg _) hB))
  have h := Matrix.det_le (abv := AbsoluteValue.abs) hentry
  simpa only [AbsoluteValue.abs_apply, nsmul_eq_mul, ← pow_mul] using h

/-- Cramer's coefficients obey the same bound when the new vector is bounded. -/
theorem abs_cramer_gram_le {w : ι → E} {u : E} {B : ℝ}
    (hB : 0 ≤ B) (hw : ∀ i, ‖w i‖ ≤ B) (hu : ‖u‖ ≤ B) (j : ι) :
    |(Matrix.gram ℝ w).cramer (fun i => ⟪w i, u⟫_ℝ) j| ≤
      (Fintype.card ι).factorial * B ^ (2 * Fintype.card ι) := by
  rw [Matrix.cramer_apply]
  have he (i k : ι) :
      |((Matrix.gram ℝ w).updateCol j (fun i => ⟪w i, u⟫_ℝ)) i k| ≤ B ^ 2 := by
    by_cases hk : k = j
    · subst k
      simp only [Matrix.updateCol_self]
      exact (abs_real_inner_le_norm _ _).trans (by simpa only [pow_two] using (mul_le_mul (hw i) hu (norm_nonneg _) hB))
    · simp only [Matrix.updateCol_ne hk, Matrix.gram_apply]
      exact (abs_real_inner_le_norm _ _).trans (by simpa only [pow_two] using (mul_le_mul (hw i) (hw k) (norm_nonneg _) hB))
  have h := Matrix.det_le (abv := AbsoluteValue.abs) he
  simpa only [AbsoluteValue.abs_apply, nsmul_eq_mul, ← pow_mul] using h

/-- A polynomial height bound for the denominator-free projection step. -/
theorem norm_gramResidual_le {w : ι → E} {u : E} {B : ℝ}
    (hB : 0 ≤ B) (hw : ∀ i, ‖w i‖ ≤ B) (hu : ‖u‖ ≤ B) :
    ‖gramResidual w u‖ ≤ (Fintype.card ι + 1).factorial *
      B ^ (2 * Fintype.card ι + 1) := by
  let A : ℝ := (Fintype.card ι).factorial * B ^ (2 * Fintype.card ι)
  have hA : 0 ≤ A := by positivity
  have hd := abs_det_gram_le hB hw
  have hc := abs_cramer_gram_le hB hw hu
  calc
    _ ≤ ‖(Matrix.gram ℝ w).det • u‖ +
        ‖∑ i, (Matrix.gram ℝ w).cramer (fun j => ⟪w j, u⟫_ℝ) i • w i‖ := norm_sub_le _ _
    _ ≤ A * B + ∑ _i : ι, A * B := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul hd hu (norm_nonneg _) hA
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hc i) (hw i) (norm_nonneg _) hA
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, A, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

/-- The same bound controls a functional whose values on the inputs are bounded.
No bound on the norm of the functional itself is needed. -/
theorem abs_apply_gramResidual_le {w : ι → E} {u : E} {B : ℝ}
    (hB : 0 ≤ B) (hw : ∀ i, ‖w i‖ ≤ B) (hu : ‖u‖ ≤ B)
    (ℓ : E →ₗ[ℝ] ℝ) (hlw : ∀ i, |ℓ (w i)| ≤ B) (hlu : |ℓ u| ≤ B) :
    |ℓ (gramResidual w u)| ≤ (Fintype.card ι + 1).factorial *
      B ^ (2 * Fintype.card ι + 1) := by
  let A : ℝ := (Fintype.card ι).factorial * B ^ (2 * Fintype.card ι)
  have hA : 0 ≤ A := by positivity
  have hd := abs_det_gram_le hB hw
  have hc := abs_cramer_gram_le hB hw hu
  simp only [gramResidual, map_sub, map_sum, map_smul, smul_eq_mul]
  calc
    _ ≤ |(Matrix.gram ℝ w).det * ℓ u| +
        |∑ i, (Matrix.gram ℝ w).cramer (fun j => ⟪w j, u⟫_ℝ) i * ℓ (w i)| := by simpa only [Real.norm_eq_abs] using (norm_sub_le
          ((Matrix.gram ℝ w).det * ℓ u)
          (∑ i, (Matrix.gram ℝ w).cramer (fun j => ⟪w j, u⟫_ℝ) i * ℓ (w i)))
    _ ≤ A * B + ∑ _i : ι, A * B := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul hd hlu (abs_nonneg _) hA
      · apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (hc i) (hlw i) (abs_nonneg _) hA
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, A, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

end WaveTurbulence.LinAlg
