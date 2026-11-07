/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeNormalization
import Mathlib.Tactic

/-! # Explicit scalar absorption in DH23 10.1 operations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem ceil_mul_scale_le {C A : ℝ} (hC : 0 ≤ C) (hA : 1 ≤ A) :
    (⌈C*A⌉₊ : ℝ) ≤ (C+1)*A := by
  have hh := Nat.ceil_lt_add_one (mul_nonneg hC (zero_le_one.trans hA))
  nlinarith only [hh,hA]

/-- The two lost circuits absorb the actual natural ceiling in the
three-label local count. The large-C1 condition is explicit. -/
theorem triple_deletion_scalar_le_one {L a δ C1 C : ℝ}
    (hL : 1 ≤ L) (ha : 0 ≤ a) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hC1 : 0 < C1) (hC : 0 ≤ C) (hlarge : C+1 ≤ C1^2) :
    (⌈C*δ⁻¹*L^(2*a)⌉₊ : ℝ)*L^(-2*a)*(C1⁻¹*δ^(1/2 : ℝ))^2 ≤ 1 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hA : 1 ≤ δ⁻¹*L^(2*a) := one_le_mul_of_one_le_of_one_le
    ((one_le_inv₀ hδ.1).mpr hδ.2) (Real.one_le_rpow hL (by linarith only [ha]))
  have hk : (⌈C*δ⁻¹*L^(2*a)⌉₊ : ℝ) ≤ (C+1)*(δ⁻¹*L^(2*a)) := by
    simpa only [mul_assoc] using ceil_mul_scale_le hC hA
  have hm := mul_le_mul_of_nonneg_right hk
    (by positivity : 0 ≤ L^(-2*a)*(C1⁻¹*δ^(1/2 : ℝ))^2)
  have hδhalf : (δ^(1/2 : ℝ))^2 = δ := by
    rw [← Real.rpow_mul_natCast hδ.1.le]
    norm_num
  have hid : (C+1)*(δ⁻¹*L^(2*a))*(L^(-2*a)*(C1⁻¹*δ^(1/2 : ℝ))^2) = (C+1)/C1^2 := by
    rw [show -2*a = -(2*a) by ring,Real.rpow_neg hL0.le,mul_pow,hδhalf]
    field_simp [hδ.1.ne']
  have hh : (C+1)/C1^2 ≤ 1 := (div_le_one (sq_pos_of_pos hC1)).mpr hlarge
  calc
    _ = (⌈C*δ⁻¹*L^(2*a)⌉₊ : ℝ)*(L^(-2*a)*(C1⁻¹*δ^(1/2 : ℝ))^2) := by ring
    _ ≤ _ := hm
    _ = _ := hid
    _ ≤ 1 := hh

/-- One lost circuit absorbs the LG pair count at a concrete source
large-L threshold. No counting or operation estimate is assumed. -/
theorem pair_deletion_scalar_le_one {L a η δ B C : ℝ}
    (hL : 1 ≤ L) (ha : η ≤ a) (hη : 0 < η)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hB : 0 ≤ B) (hB1 : B ≤ 1) (hC : 0 ≤ C)
    (hlarge : ((C+1)*δ⁻¹)^(η⁻¹) ≤ L) :
    (⌈C*δ⁻¹*L^(a-η)⌉₊ : ℝ)*L^(-a)*B ≤ 1 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hA : 1 ≤ δ⁻¹*L^(a-η) := one_le_mul_of_one_le_of_one_le
    ((one_le_inv₀ hδ.1).mpr hδ.2) (Real.one_le_rpow hL (sub_nonneg.mpr ha))
  have hk : (⌈C*δ⁻¹*L^(a-η)⌉₊ : ℝ) ≤ (C+1)*(δ⁻¹*L^(a-η)) := by
    simpa only [mul_assoc] using ceil_mul_scale_le hC hA
  have hK0 : 0 ≤ (C+1)*δ⁻¹ := mul_nonneg (by linarith only [hC]) (inv_nonneg.mpr hδ.1.le)
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hlarge hη.le
  rw [← Real.rpow_mul hK0,inv_mul_cancel₀ hη.ne',Real.rpow_one] at hp
  have hh : (C+1)*δ⁻¹*L^(-η) ≤ 1 := by
    rw [Real.rpow_neg hL0.le,← div_eq_mul_inv]
    exact (div_le_one (Real.rpow_pos_of_pos hL0 η)).mpr hp
  have hm := mul_le_mul hk hB1 hB (by positivity : 0 ≤ (C+1)*(δ⁻¹*L^(a-η)))
  have hm' := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hL0.le (-a))
  have hid : (C+1)*(δ⁻¹*L^(a-η))*1*L^(-a) = (C+1)*δ⁻¹*L^(-η) := by
    rw [mul_one]
    calc
      _ = ((C+1)*δ⁻¹)*(L^(a-η)*L^(-a)) := by ring
      _ = _ := by rw [← Real.rpow_add hL0]; congr 2; ring
  calc
    _ = ((⌈C*δ⁻¹*L^(a-η)⌉₊ : ℝ)*B)*L^(-a) := by ring
    _ ≤ _ := hm'
    _ = _ := hid
    _ ≤ 1 := hh

end WaveTurbulence.MoleProp
