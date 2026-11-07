/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionScalars
import Mathlib.Tactic

/-! # Exact cancellation of the actual ladder factor in DH23 laddersharp -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem four_label_deletion_scalar_le_one {L a δ C1 C X : ℝ}
    (hL : 1 ≤ L) (ha : 1 ≤ a) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hC1 : 0 < C1) (hC : 0 ≤ C) (hlarge : C+1 ≤ C1^2)
    (hX : 1 ≤ X) (hXlog : X ≤ Real.log L^2) :
    (⌈C*δ⁻¹*L^(2*a)*X⁻¹⌉₊ : ℝ)*L^(-2*a)*(C1⁻¹*δ^(1/2 : ℝ))^2*X ≤ 1 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hlog : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hlogpow : Real.log L^2 ≤ L^2 := pow_le_pow_left₀ (Real.log_nonneg hL) hlog 2
  have hpow : L^2 ≤ L^(2*a) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num; linarith only [ha])
  have hdi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hmul : L^(2*a) ≤ δ⁻¹*L^(2*a) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hdi (Real.rpow_nonneg hL0.le (2*a))
  have hXA : X ≤ δ⁻¹*L^(2*a) := hXlog.trans (hlogpow.trans (hpow.trans hmul))
  have hA : 1 ≤ δ⁻¹*L^(2*a)*X⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (one_le_div₀ hX0).mpr hXA
  have hk : (⌈C*δ⁻¹*L^(2*a)*X⁻¹⌉₊ : ℝ) ≤ (C+1)*(δ⁻¹*L^(2*a)*X⁻¹) := by
    simpa only [mul_assoc] using ceil_mul_scale_le hC hA
  have hm := mul_le_mul_of_nonneg_right hk
    (by positivity : 0 ≤ L^(-2*a)*(C1⁻¹*δ^(1/2 : ℝ))^2*X)
  have hδhalf : (δ^(1/2 : ℝ))^2 = δ := by
    rw [← Real.rpow_mul_natCast hδ.1.le]
    norm_num
  have hid : (C+1)*(δ⁻¹*L^(2*a)*X⁻¹)*(L^(-2*a)*(C1⁻¹*δ^(1/2 : ℝ))^2*X) = (C+1)/C1^2 := by
    rw [show -2*a=-(2*a) by ring,Real.rpow_neg hL0.le,mul_pow,hδhalf]
    field_simp [hδ.1.ne',hX0.ne']
  calc
    _ = (⌈C*δ⁻¹*L^(2*a)*X⁻¹⌉₊ : ℝ)*(L^(-2*a)*(C1⁻¹*δ^(1/2 : ℝ))^2*X) := by ring
    _ ≤ _ := hm
    _ = _ := hid
    _ ≤ 1 := (div_le_one (sq_pos_of_pos hC1)).mpr hlarge

end WaveTurbulence.MoleProp
