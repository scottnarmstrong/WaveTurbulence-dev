/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Structural integer coordinates supplied by the link parametrization

TARGET (incohproof1)–(3). C2's `incoh_unimodular` supplies the two
integer matrices and their inverse identities after enumerating the plus
leaves and the root/link coordinates. No analytic estimate is a field.
-/

public section
noncomputable section
open Matrix
open scoped Kronecker

namespace WaveTurbulence.Incoh

/-- Finite integer coordinate data of the root and `2n` link variables. -/
structure IntegerLeafCoordinates (n : ℕ) where
  forward : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℤ
  backward : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℤ
  forward_mul_backward : forward * backward = 1
  backward_mul_forward : backward * forward = 1
  root_column : ∀ i, forward i 0 = 1
  root_row_mem : ∀ i, backward 0 i ∈ ({-1, 0, 1} : Finset ℤ)

/-- The source coefficients `σ` are the inverse root row, not independently chosen weights. -/
@[expose] def IntegerLeafCoordinates.sigma {n : ℕ} (P : IntegerLeafCoordinates n)
    (i : Fin (2 * n + 1)) : ℤ := P.backward 0 i

/-- The sum of the actual root-recovery coefficients is exactly one. -/
theorem IntegerLeafCoordinates.sum_sigma {n : ℕ} (P : IntegerLeafCoordinates n) :
    ∑ i, P.sigma i = 1 := by
  have h := congrArg (fun A : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℤ => A 0 0)
    P.backward_mul_forward
  simpa only [sigma, Matrix.mul_apply, P.root_column, mul_one, Matrix.one_apply_eq] using h

/-- Inverse integer matrices have determinant of absolute value one. -/
theorem IntegerLeafCoordinates.abs_det_forward {n : ℕ} (P : IntegerLeafCoordinates n) :
    |P.forward.det| = 1 := by
  have h : P.forward.det * P.backward.det = 1 := by
    rw [← Matrix.det_mul, P.forward_mul_backward, Matrix.det_one]
  have hu : IsUnit P.forward.det := isUnit_iff_dvd_one.mpr ⟨P.backward.det, h.symm⟩
  exact Int.isUnit_iff_abs_eq.mp hu

/-- The actual spatial block matrix acts by the same integer transform in every momentum coordinate. -/
@[expose] def IntegerLeafCoordinates.blockMatrix {n : ℕ} (P : IntegerLeafCoordinates n) (d : ℕ) :
    Matrix (Fin ((2 * n + 1) * d)) (Fin ((2 * n + 1) * d)) ℝ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    ((P.forward.map (fun z => (z : ℝ))) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℝ))

/-- The full spatial change of variables preserves Lebesgue volume in every dimension. -/
theorem IntegerLeafCoordinates.abs_det_blockMatrix {n : ℕ} (P : IntegerLeafCoordinates n) (d : ℕ) :
    |(P.blockMatrix d).det| = 1 := by
  rw [blockMatrix, Matrix.det_reindex_self, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one,
    abs_pow, ← Int.cast_det]
  have h : |(P.forward.det : ℝ)| = 1 := by exact_mod_cast P.abs_det_forward
  rw [h, one_pow]

end WaveTurbulence.Incoh
