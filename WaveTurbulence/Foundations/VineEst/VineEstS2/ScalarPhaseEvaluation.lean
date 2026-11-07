/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9OriginCoefficients

/-! # Exact scalar integer evaluations inside the physical momentum carrier -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2

noncomputable def scalarMomentum (z : ℤ) : Mom 1 := WithLp.toLp 2 (fun _ => (z : ℝ))

noncomputable def scalarMomentumHom : ℤ →+ Mom 1 where
  toFun := scalarMomentum
  map_zero' := by ext i; simp [scalarMomentum]
  map_add' := by intro a b; ext i; simp [scalarMomentum]

theorem inner_scalarMomentum (a b : ℤ) :
    inner ℝ (scalarMomentum a) (scalarMomentum b) = ((a*b : ℤ) : ℝ) := by
  simp [PiLp.inner_apply,scalarMomentum,mul_comm]

/-- Finite integer forms commute exactly with the physical scalar map. -/
theorem scalarMomentum_linearForm {α : Type*} [Fintype α] (a x : α → ℤ) :
    (∑ i, a i • scalarMomentum (x i)) = scalarMomentum (integerLinearForm a x) := by
  change (∑ i, a i • scalarMomentumHom (x i)) = scalarMomentumHom (integerLinearForm a x)
  rw [integerLinearForm,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [zsmul_eq_mul,Int.cast_id] using (map_zsmul scalarMomentumHom (a i) (x i)).symm

end WaveTurbulence.VineEstS2
