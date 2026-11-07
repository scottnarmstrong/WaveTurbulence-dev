/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionScalars
import Mathlib.Tactic

/-! # The five-label gain absorbs the one lost ladder-position factor -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem log_pow_two_le_rpow {L ε : ℝ} (hL : 1 ≤ L) (hε : 0 < ε) :
    Real.log L ^ 2 ≤ (2/ε)^2*L^ε := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hh := Real.log_le_rpow_div hL0.le (by linarith only [hε] : 0 < ε/2)
  have hp := pow_le_pow_left₀ (Real.log_nonneg hL) hh 2
  have he : (L^(ε/2)/(ε/2))^2 = (2/ε)^2*L^ε := by
    rw [div_eq_mul_inv,mul_pow,← Real.rpow_mul_natCast hL0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*2=ε by ring,show (ε/2)⁻¹=2/ε by field_simp]
    ring
  exact hp.trans_eq he

theorem five_label_deletion_scalar_le_one {L a g δ B C : ℝ}
    (hL : 1 ≤ L) (hg : 0 < g) (ha : g ≤ a) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hB : 0 ≤ B) (hB1 : B ≤ 1) (hC : 0 ≤ C)
    (hlarge : ((C+1)*δ⁻¹^2*(4/g)^2)^(2/g) ≤ L) :
    (⌈C*δ⁻¹^2*L^(3*a-g)⌉₊ : ℝ)*L^(-3*a)*B^3*Real.log L^2 ≤ 1 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hdi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hdi2 : 1 ≤ δ⁻¹^2 := one_le_pow₀ hdi
  have hA : 1 ≤ δ⁻¹^2*L^(3*a-g) := one_le_mul_of_one_le_of_one_le hdi2
    (Real.one_le_rpow hL (by linarith only [ha,hg]))
  have hk : (⌈C*δ⁻¹^2*L^(3*a-g)⌉₊ : ℝ) ≤ (C+1)*(δ⁻¹^2*L^(3*a-g)) := by
    simpa only [mul_assoc] using ceil_mul_scale_le hC hA
  have hlog := log_pow_two_le_rpow hL (by linarith only [hg] : 0 < g/2)
  rw [show 2/(g/2)=4/g by field_simp [hg.ne'] <;> ring] at hlog
  have hB3 : B^3 ≤ 1 := pow_le_one₀ hB hB1
  have h1 := mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hL0.le (-3*a))
  have h2 := mul_le_mul h1 hB3 (pow_nonneg hB _) (by positivity : 0 ≤ (C+1)*(δ⁻¹^2*L^(3*a-g))*L^(-3*a))
  have h3 := mul_le_mul h2 hlog (sq_nonneg (Real.log L))
    (by positivity : 0 ≤ (C+1)*(δ⁻¹^2*L^(3*a-g))*L^(-3*a)*1)
  let K := (C+1)*δ⁻¹^2*(4/g)^2
  have hK : 0 ≤ K := by unfold K; exact mul_nonneg (mul_nonneg (by linarith only [hC]) (sq_nonneg _)) (sq_nonneg _)
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hK _) hlarge (by linarith only [hg] : 0 ≤ g/2)
  rw [← Real.rpow_mul hK,show (2/g)*(g/2)=1 by field_simp [hg.ne'] <;> ring,Real.rpow_one] at hp
  have hlast : K*L^(-(g/2)) ≤ 1 := by
    rw [Real.rpow_neg hL0.le,← div_eq_mul_inv]
    exact (div_le_one (Real.rpow_pos_of_pos hL0 (g/2))).mpr hp
  apply h3.trans
  have hid : (C+1)*(δ⁻¹^2*L^(3*a-g))*L^(-3*a)*1*((4/g)^2*L^(g/2)) = K*L^(-(g/2)) := by
    rw [mul_one]
    calc
      _ = K*(L^(3*a-g)*L^(-3*a)*L^(g/2)) := by dsimp only [K]; ring
      _ = _ := by rw [← Real.rpow_add hL0,← Real.rpow_add hL0]; congr 2; ring
  exact hid.le.trans hlast

end WaveTurbulence.MoleProp
