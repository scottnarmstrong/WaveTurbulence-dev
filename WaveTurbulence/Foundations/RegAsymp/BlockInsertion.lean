/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ClassJR.MCSob
import Mathlib.Tactic

/-! # ℓ¹ insertion of frozen and surviving coefficient blocks -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open ClassJR WithLp

/-- Extend the left block by zero on every surviving variable. -/
def sumLeftZeroL1 {ι κ : Type} [Fintype ι] [Fintype κ] : L1 ι →ₗᵢ[ℝ] L1 (ι ⊕ κ) where
  toFun α := toLp 1 (Sum.elim (fun i => α i) (fun _ => (0:ℝ)))
  map_add' α β := by ext i; cases i <;> simp
  map_smul' r α := by ext i; cases i <;> simp
  norm_map' α := by rw [PiLp.norm_eq_of_L1,PiLp.norm_eq_of_L1]; simp

/-- Extend the surviving block by zero on every frozen variable. -/
def sumRightZeroL1 {ι κ : Type} [Fintype ι] [Fintype κ] : L1 κ →ₗᵢ[ℝ] L1 (ι ⊕ κ) where
  toFun β := toLp 1 (Sum.elim (fun _ => (0:ℝ)) (fun i => β i))
  map_add' α β := by ext i; cases i <;> simp
  map_smul' r α := by ext i; cases i <;> simp
  norm_map' α := by rw [PiLp.norm_eq_of_L1,PiLp.norm_eq_of_L1]; simp

/-- Sup norm to ℓ¹ loses only the number of frozen coordinates. -/
theorem norm_toL1_le_card (r : ℕ) : ‖toL1 r‖ ≤ (r:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _)
  intro α
  rw [toL1_apply,PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _i : Fin r, ‖α‖ := Finset.sum_le_sum (fun i _ => norm_le_pi_norm α i)
    _ = _ := by simp

/-- The full affine insertion of two blocks. -/
theorem sumBlocks_toLp_eq {ι κ : Type} [Fintype ι] [Fintype κ] (α : ι → ℝ) (β : κ → ℝ) :
    toLp 1 (Sum.elim α β) = sumLeftZeroL1 (toLp 1 α)+sumRightZeroL1 (toLp 1 β) := by
  ext i
  cases i <;> simp [sumLeftZeroL1,sumRightZeroL1]

end WaveTurbulence.RegAsymp
