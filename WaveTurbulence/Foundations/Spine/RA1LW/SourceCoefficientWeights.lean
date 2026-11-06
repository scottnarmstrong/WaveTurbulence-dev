/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalGlobalProfile

/-! # Norm bounds for the original finite physical source weights -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp

/-- Every original garden branching factor has unit modulus. -/
theorem norm_garden_zeta {w : ℕ} (G : Garden w) : ‖G.zeta‖ = 1 := by
  unfold Garden.zeta
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro b _
  rcases Int.units_eq_one_or (G.sign b.toNode) with hb | hb <;>
    simp only [hb,Units.val_one,Units.val_neg,Int.cast_one,Int.cast_neg,mul_one,mul_neg,
      norm_neg,Complex.norm_I]

/-- The original positive inverse source weight has norm at most one. -/
theorem norm_original_source_weight_le_one (Z : Finset (Fin 2 × TTree.Path)) :
    ‖∏ z ∈ Z, ((Cancel.zetaA z:ℂ)*Real.pi*Complex.I)⁻¹‖ ≤ 1 := by
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro z _
  rcases Cancel.zetaA_pm z with hz | hz
  all_goals
    simp only [hz,Int.cast_one,Int.cast_neg,one_mul,neg_mul,norm_inv,norm_neg,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
    exact inv_le_one_of_one_le₀ (by linarith only [Real.two_le_pi] : (1:ℝ) ≤ Real.pi)

/-- The exact correction from physical2delta to the original coupling
never enlarges the source error envelope. -/
theorem norm_inverse_four_pow_le_one (n : ℕ) : ‖((4:ℂ)^n)⁻¹‖ ≤ 1 := by
  rw [norm_inv,norm_pow]
  norm_num only [Complex.norm_ofNat]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4))

end WaveTurbulence.RA1Leafwise
