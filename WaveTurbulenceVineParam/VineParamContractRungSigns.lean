/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamReferenceShear
import Mathlib.Tactic

/-! # Normalizing an inserted rung to the exact signed V4 phase slots -/

public section
namespace WaveTurbulence.Vine.Param
variable {E : Type*} [AddCommGroup E]

/-- The lower source row becomes the contract s row after one sign flip. -/
@[expose] def rungSignEquiv : (E×E) ≃ (E×E) where
  toFun := fun xy => (-xy.1,xy.2)
  invFun := fun xy => (-xy.1,xy.2)
  left_inv := by intro xy; simp
  right_inv := by intro xy; simp

namespace RungPattern

/-- Exact gap-correction coefficients after the physical-gap sign and the
contract coordinate sign have been incorporated. -/
@[expose] def contractCorrection (P : RungPattern) (ε : ℤ) : Fin 3 → ℤ :=
  ![-ε*P.coefficients 0,ε*P.coefficients 1,ε*ε*P.coefficients 2]

/-- A cap contains neither joint or just one, so the contract coefficients
remain ternary in every source orientation. -/
theorem contractCorrection_unit (P : RungPattern) (ε : ℤ)
    (hε : ε ∈ ({-1,0,1} : Finset ℤ)) :
    ∀ c,contractCorrection P ε c ∈ ({-1,0,1} : Finset ℤ) := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hε
  rcases hε with rfl | rfl | rfl <;> cases P <;> decide

/-- A nonzero physical gap retains a nonzero paired correction, including
one-double-bond type II. -/
theorem contractCorrection_nonzero (P : RungPattern) (ε : ℤ)
    (hε : ε ∈ ({-1,0,1} : Finset ℤ)) (hne : ε ≠ 0) :
    contractCorrection P ε 0 ≠ 0 ∨ contractCorrection P ε 1 ≠ 0 := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hε
  rcases hε with rfl | rfl | rfl
  · cases P <;> decide
  · exact (hne rfl).elim
  · cases P <;> decide

/-- Evaluation of the physical correction yields precisely its contract
linear gap term. All scalar casts are explicit. -/
theorem contractCorrection_phase {d : ℕ} (P : RungPattern) (ε : ℤ) (r x y : Mom d) :
    inner ℝ (ε • r) (P.correction (ε • r) (-x,y))=
      inner ℝ r ((contractCorrection P ε 0 : ℝ) • x+
        (contractCorrection P ε 1 : ℝ) • y+(contractCorrection P ε 2 : ℝ) • r) := by
  rw [P.correction_coefficients]
  change inner ℝ (ε • r) (P.coefficients 0 • (-x)+P.coefficients 1 • y+
    P.coefficients 2 • (ε • r))=inner ℝ r
      (((-ε*P.coefficients 0 : ℤ) : ℝ) • x+
        ((ε*P.coefficients 1 : ℤ) : ℝ) • y+((ε*ε*P.coefficients 2 : ℤ) : ℝ) • r)
  simp only [← Int.cast_smul_eq_zsmul ℝ,Int.cast_mul,Int.cast_neg,inner_add_right,
    inner_neg_right,real_inner_smul_left,real_inner_smul_right]
  ring

end RungPattern
end WaveTurbulence.Vine.Param
