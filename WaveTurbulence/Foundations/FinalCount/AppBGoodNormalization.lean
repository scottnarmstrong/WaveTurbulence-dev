/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairGoodGain
public import WaveTurbulence.Foundations.FinalCount.AppBFineNormalization
import Mathlib.Tactic

/-! # Absorbing bounded ladder losses in a good operation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Filter
open scoped ENNReal

theorem appb_good_log_coefficient_eventual (C a γ0 : ℝ) (b : ℕ)
    (hC : 0 ≤ C) (hγ0 : 0 < γ0) (ha : 5/8 < a) :
    ∀ᶠ L : ℝ in atTop,C*(Real.log L)^b*L^(-a*γ0) ≤ L^(-5*γ0/8) := by
  have hraw := appb_log_coefficient_eventual C 1 (-a*γ0) (-5*γ0/8) b
    (by nlinarith only [ha,hγ0])
  filter_upwards [hraw,eventually_ge_atTop (1 : ℝ)] with L hb hL
  have hlog := Real.log_nonneg hL
  have hp : (Real.log L)^b ≤ (1+Real.log L)^b :=
    pow_le_pow_left₀ hlog (by linarith only [hlog]) b
  calc
    _ ≤ C*(1+Real.log L)^b*L^(-a*γ0) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp hC) (Real.rpow_nonneg (zero_le_one.trans hL) _)
    _ ≤ _ := by simpa only [inv_one,mul_one] using hb

theorem appb_normalization_step_nat (χ : ℤ) (r : ℕ) (L D B H : ℝ) (hL : 0 < L) (hB : B ≠ 0) :
    L^(-D*((χ+(r : ℤ) : ℤ) : ℝ))*B^(χ+(r : ℤ))*H =
      (L^(-D*(r : ℝ))*B^r)*(L^(-D*(χ : ℝ))*B^χ*H) := by
  have he : -D*((χ+(r : ℤ) : ℤ) : ℝ) = -D*(χ : ℝ)+(-D*(r : ℝ)) := by push_cast; ring
  rw [he,Real.rpow_add hL,zpow_add₀ hB,zpow_natCast]
  ring

/-- Conditional scalar assembly helper for good operations. Source
exports separately establish raw counting, graph rank, link loss and the
eventual coefficient estimate. It remains an inequality at zero counts. -/
theorem appb_good_normalization_of_raw (Epre Epos : ℝ≥0∞) (χ : ℤ) (r b : ℕ)
    (L D B Hpre Hpos C a γ0 : ℝ) (hL : 1 ≤ L) (hB : 0 < B) (hB1 : B ≤ 1) (hC : 0 ≤ C)
    (hlinks : Hpre ≤ (Real.log L)^b*Hpos)
    (hcoef : C*(Real.log L)^b*L^(-a*γ0) ≤ L^(-5*γ0/8))
    (hraw : Epre ≤ ENNReal.ofReal (C*L^(D*(r : ℝ)-a*γ0))*Epos) :
    Epre*ENNReal.ofReal (L^(-D*((χ+(r : ℤ) : ℤ) : ℝ))*B^(χ+(r : ℤ))*Hpre) ≤
      ENNReal.ofReal (L^(-5*γ0/8))*(Epos*ENNReal.ofReal (L^(-D*(χ : ℝ))*B^χ*Hpos)) := by
  have hLp := zero_lt_one.trans_le hL
  have hlog := Real.log_nonneg hL
  have hbase : 0 ≤ L^(-D*(χ : ℝ))*B^χ := by positivity
  have hstep : 0 ≤ L^(-D*(r : ℝ))*B^r := by positivity
  have hfac : 0 ≤ L^(-D*(r : ℝ))*B^r*(Real.log L)^b := by positivity
  have hA : 0 ≤ C*L^(D*(r : ℝ)-a*γ0) := by positivity
  have hpre : L^(-D*((χ+(r : ℤ) : ℤ) : ℝ))*B^(χ+(r : ℤ))*Hpre ≤
      (L^(-D*(r : ℝ))*B^r*(Real.log L)^b)*(L^(-D*(χ : ℝ))*B^χ*Hpos) := by
    rw [appb_normalization_step_nat χ r L D B Hpre hLp hB.ne']
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlinks hbase) hstep).trans_eq (by ring)
  have hpow : L^(D*(r : ℝ)-a*γ0)*L^(-D*(r : ℝ)) = L^(-a*γ0) := by
    rw [← Real.rpow_add hLp]
    congr 1
    ring
  have hcombined : (C*L^(D*(r : ℝ)-a*γ0))*(L^(-D*(r : ℝ))*B^r*(Real.log L)^b) ≤ L^(-5*γ0/8) := by
    calc
      _ = C*(Real.log L)^b*(L^(D*(r : ℝ)-a*γ0)*L^(-D*(r : ℝ)))*B^r := by ring
      _ = C*(Real.log L)^b*L^(-a*γ0)*B^r := by rw [hpow]
      _ ≤ C*(Real.log L)^b*L^(-a*γ0) := mul_le_of_le_one_right (by positivity) (pow_le_one₀ hB.le hB1)
      _ ≤ _ := hcoef
  have hw := ENNReal.ofReal_le_ofReal hpre
  rw [ENNReal.ofReal_mul hfac] at hw
  calc
    _ ≤ (ENNReal.ofReal (C*L^(D*(r : ℝ)-a*γ0))*Epos)*
        ENNReal.ofReal (L^(-D*((χ+(r : ℤ) : ℤ) : ℝ))*B^(χ+(r : ℤ))*Hpre) := mul_le_mul_left hraw _
    _ ≤ (ENNReal.ofReal (C*L^(D*(r : ℝ)-a*γ0))*Epos)*
        (ENNReal.ofReal (L^(-D*(r : ℝ))*B^r*(Real.log L)^b)*
          ENNReal.ofReal (L^(-D*(χ : ℝ))*B^χ*Hpos)) := mul_le_mul_right hw _
    _ = ENNReal.ofReal ((C*L^(D*(r : ℝ)-a*γ0))*(L^(-D*(r : ℝ))*B^r*(Real.log L)^b))*
        (Epos*ENNReal.ofReal (L^(-D*(χ : ℝ))*B^χ*Hpos)) := by
      rw [ENNReal.ofReal_mul hA]
      ring
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hcombined) _

end WaveTurbulence.Mole
