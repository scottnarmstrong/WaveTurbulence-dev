/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBFineNormalization
import Mathlib.Tactic

/-! # Scalar normalization for a circuit-rank-two normal removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal

theorem appb_normalization_step_two (χ : ℤ) (L D B H : ℝ) (hL : 0 < L) (hB : B ≠ 0) :
    L^(-D*((χ+2 : ℤ) : ℝ))*B^(χ+2)*H =
      (L^(-2*D)*B^2)*(L^(-D*(χ : ℝ))*B^χ*H) := by
  have he : -D*((χ+2 : ℤ) : ℝ) = -D*(χ : ℝ)+(-2*D) := by push_cast; ring
  rw [he,Real.rpow_add hL,zpow_add₀ hB]
  norm_num only [zpow_ofNat]
  ring

/-- Conditional scalar helper for a proved triple count. A sufficiently
large fixed C1 absorbs its dimension-dependent constant exactly. -/
theorem appb_normal_normalization_of_raw (Epre Epos : ℝ≥0∞) (χ : ℤ)
    (L D δ C1 C H : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hC1 : 1 ≤ C1)
    (hC : C ≤ C1) (hC0 : 0 ≤ C)
    (hraw : Epre ≤ ENNReal.ofReal (C*δ⁻¹*L^(2*D))*Epos) :
    Epre*ENNReal.ofReal (L^(-D*((χ+2 : ℤ) : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^(χ+2)*H) ≤
      Epos*ENNReal.ofReal (L^(-D*(χ : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^χ*H) := by
  have hCpos := zero_lt_one.trans_le hC1
  have hB : 0 < C1⁻¹*δ^(1/2 : ℝ) := mul_pos (inv_pos.mpr hCpos) (Real.rpow_pos_of_pos hδ _)
  have hfac : 0 ≤ L^(-2*D)*(C1⁻¹*δ^(1/2 : ℝ))^2 := by positivity
  have hpow : 0 ≤ C*δ⁻¹*L^(2*D) := by positivity
  have hsq : (δ^(1/2 : ℝ))^2 = δ := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hδ.le
  have hcancel : L^(2*D)*L^(-2*D) = 1 := by
    rw [← Real.rpow_add hL]
    convert Real.rpow_zero L using 1 <;> ring
  have hcoef : (C*δ⁻¹*L^(2*D))*(L^(-2*D)*(C1⁻¹*δ^(1/2 : ℝ))^2) ≤ 1 := by
    calc
      _ = C*δ⁻¹*(L^(2*D)*L^(-2*D))*(C1⁻¹*δ^(1/2 : ℝ))^2 := by ring
      _ = C*(C1⁻¹)^2 := by
        rw [hcancel,mul_pow,hsq]
        field_simp
        <;> ring
      _ ≤ C1*(C1⁻¹)^2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)
      _ = C1⁻¹ := by field_simp
      _ ≤ 1 := (inv_le_one₀ hCpos).mpr hC1
  rw [appb_normalization_step_two χ L D _ H hL hB.ne',ENNReal.ofReal_mul hfac]
  calc
    _ = (Epre*ENNReal.ofReal (L^(-2*D)*(C1⁻¹*δ^(1/2 : ℝ))^2))*
        ENNReal.ofReal (L^(-D*(χ : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^χ*H) := by ring
    _ ≤ ((ENNReal.ofReal (C*δ⁻¹*L^(2*D))*Epos)*
        ENNReal.ofReal (L^(-2*D)*(C1⁻¹*δ^(1/2 : ℝ))^2))*
        ENNReal.ofReal (L^(-D*(χ : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^χ*H) :=
      mul_le_mul_left (mul_le_mul_left hraw _) _
    _ = ENNReal.ofReal ((C*δ⁻¹*L^(2*D))*(L^(-2*D)*(C1⁻¹*δ^(1/2 : ℝ))^2))*
        (Epos*ENNReal.ofReal (L^(-D*(χ : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^χ*H)) := by
      rw [ENNReal.ofReal_mul hpow]
      ring
    _ ≤ _ := by
      have hh : ENNReal.ofReal ((C*δ⁻¹*L^(2*D))*(L^(-2*D)*(C1⁻¹*δ^(1/2 : ℝ))^2)) ≤ 1 := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hcoef
      simpa only [one_mul] using mul_le_mul_left hh (Epos*ENNReal.ofReal (L^(-D*(χ : ℝ))*(C1⁻¹*δ^(1/2 : ℝ))^χ*H))

end WaveTurbulence.Mole
