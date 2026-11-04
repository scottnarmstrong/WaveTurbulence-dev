/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ShapeFacts
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Group.Int.Units
import Mathlib.Tactic

/-!
# Unimodularity of the exact sumint change of lattice variables

The two inverse identities in the datum imply determinant plus or minus
one. This supplies the volume-preserving change in TARGET Step 1.
-/

public section

namespace WaveTurbulence.Sumint

/-- The supplied integer inverse forces a unit determinant. -/
theorem determinant_isUnit {d : ℕ} (D : SumintDatum d) : IsUnit D.T₁.det := by
  classical
  exact Matrix.isUnit_det_of_left_inverse D.T₁inv_mul

/-- The determinant of the integer change of variables is exactly plus or minus one. -/
theorem determinant_eq_one_or_neg_one {d : ℕ} (D : SumintDatum d) :
    D.T₁.det = 1 ∨ D.T₁.det = -1 :=
  Int.isUnit_iff.mp (determinant_isUnit D)

/-- The corresponding real matrix has absolute determinant one, with no dimension-dependent loss. -/
theorem abs_real_determinant_eq_one {d : ℕ} (D : SumintDatum d) :
    |(D.T₁.map (Int.castRingHom ℝ)).det| = 1 := by
  classical
  change |(D.T₁.map (fun z : ℤ => (z : ℝ))).det| = 1
  rw [← Int.cast_det]
  rcases determinant_eq_one_or_neg_one D with h | h <;> simp [h]

/-- The source matrix gives an actual bijection of integer slot coordinates. -/
@[expose] noncomputable def integerSlotEquiv {d : ℕ} (D : SumintDatum d) :
    (D.S.VIdx → ℤ) ≃ (D.S.VIdx → ℤ) where
  toFun := D.T₁.mulVec
  invFun := D.T₁inv.mulVec
  left_inv x := by rw [Matrix.mulVec_mulVec, D.T₁inv_mul, Matrix.one_mulVec]
  right_inv x := by rw [Matrix.mulVec_mulVec, D.T₁_mul, Matrix.one_mulVec]

/-- Acting separately on spatial coordinates gives the full lattice-input bijection. -/
@[expose] noncomputable def integerBlockEquiv {d : ℕ} (D : SumintDatum d) :
    (D.S.VIdx → Fin d → ℤ) ≃ (D.S.VIdx → Fin d → ℤ) :=
  ((Equiv.piComm (fun _ : D.S.VIdx => fun _ : Fin d => ℤ)).trans
    (Equiv.piCongrRight (fun _ : Fin d => integerSlotEquiv D))).trans
      (Equiv.piComm (fun _ : Fin d => fun _ : D.S.VIdx => ℤ))

/-- Its coordinates are the literal integer matrix sums. -/
theorem integerBlockEquiv_apply {d : ℕ} (D : SumintDatum d)
    (x : D.S.VIdx → Fin d → ℤ) (v : D.S.VIdx) (j : Fin d) :
    integerBlockEquiv D x v j = ∑ w, D.T₁ v w * x w j := rfl

/-- The real scalar-slot transformation preserves Lebesgue measure exactly. -/
theorem real_slot_measurePreserving {d : ℕ} (D : SumintDatum d) :
    MeasureTheory.MeasurePreserving (Matrix.toLin' (D.T₁.map (Int.castRingHom ℝ))) := by
  classical
  have ha := abs_real_determinant_eq_one D
  have hn : (D.T₁.map (Int.castRingHom ℝ)).det ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at ha
    norm_num at ha
  refine ⟨(Matrix.toLin' (D.T₁.map (Int.castRingHom ℝ))).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hn]
  simp only [abs_inv, ha, inv_one, ENNReal.ofReal_one, one_smul]

end WaveTurbulence.Sumint
