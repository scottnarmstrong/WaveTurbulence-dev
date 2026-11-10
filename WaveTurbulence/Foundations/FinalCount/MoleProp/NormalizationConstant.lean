/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeNormalization
import Mathlib.Tactic

/-! # Exact rescaling of the exponential counting constant -/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem freeNormalization_change_constant (M : Molecule V D) {d : ℕ}
    (L γ δ Cold Cnew : ℝ) (hCold : Cold ≠ 0) (P : Finset V → ℝ) :
    freeNormalization M (d := d) L γ δ Cnew P =
      (Cold/Cnew)^M.circuitRank * freeNormalization M (d := d) L γ δ Cold P := by
  have he : Cnew⁻¹*δ^(1/2 : ℝ) = (Cold/Cnew)*(Cold⁻¹*δ^(1/2 : ℝ)) := by
    calc
      _ = (Cold*Cold⁻¹)*(Cnew⁻¹*δ^(1/2 : ℝ)) := by rw [mul_inv_cancel₀ hCold,one_mul]
      _ = _ := by ring
  unfold freeNormalization
  rw [he,mul_zpow]
  ring

theorem countAFree_change_constant (M : Molecule V D) {d : ℕ}
    (L γ δ Cold Cnew : ℝ) (hCold : 0 < Cold) (hCnew : 0 < Cnew)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    countAFree M L γ δ Cnew w Adm P =
      ENNReal.ofReal ((Cold/Cnew)^M.circuitRank) * countAFree M L γ δ Cold w Adm P := by
  rw [countAFree_eq_normalization,countAFree_eq_normalization,
    freeNormalization_change_constant M L γ δ Cold Cnew hCold.ne' P,
    ENNReal.ofReal_mul (zpow_nonneg (div_pos hCold hCnew).le _)]
  ring

end WaveTurbulence.MoleProp
