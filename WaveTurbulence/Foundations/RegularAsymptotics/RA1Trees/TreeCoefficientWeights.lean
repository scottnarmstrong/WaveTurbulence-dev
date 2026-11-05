/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeSpecialTransport
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Unit bounds on the original coefficient and garden phases -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset

/-- Every original inverse special-variable factor has modulus at most one. -/
theorem tree_coefficient_weight_norm_le (Z : Finset ClassJR.Addr) :
    ‖∏ z ∈ Z, ((ClassJR.nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹‖ ≤ 1 := by
  rw [norm_prod]
  apply prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro z _
  have hn : ‖((ClassJR.nodeSgn z:ℂ)*Real.pi*Complex.I)‖=Real.pi := by
    rcases ClassJR.nodeSgn_eq z with h|h <;>
      simp only [h,Int.cast_one,Int.cast_neg,norm_mul,norm_one,norm_neg,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,one_mul,mul_one]
  rw [norm_inv,hn]
  exact inv_le_one_of_one_le₀ (by linarith only [Real.pi_gt_three])

/-- The original garden phase is a product of unit-modulus branching factors. -/
theorem tree_garden_zeta_norm {w : ℕ} (G : Garden w) : ‖G.zeta‖=1 := by
  unfold Garden.zeta
  rw [norm_prod]
  apply prod_eq_one
  intro b _
  rcases Int.units_eq_one_or (G.sign b.toNode) with h|h <;>
    simp only [h,Units.val_one,Units.val_neg,Int.cast_one,Int.cast_neg,
      norm_mul,Complex.norm_I,norm_one,norm_neg,one_mul]

/-- The exact physical conversion factor contributes no growth in norm. -/
theorem tree_inverse_four_pow_norm_le (n : ℕ) : ‖((4:ℂ)^n)⁻¹‖ ≤ 1 := by
  rw [norm_inv,norm_pow,show ‖(4:ℂ)‖=4 by norm_num]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4))

end WaveTurbulence.RegAsymp
