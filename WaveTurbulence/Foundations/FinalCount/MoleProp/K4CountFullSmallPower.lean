/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountSmallPower
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountCutoff
import Mathlib.Tactic

/-! # Full-base small-sphere branch above the source coefficient cutoff

The cutoff makes the actual strip factor uniform. The resulting fiber
power combines with the full triple count to leave 1.05 gamma-zero.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

noncomputable def k4FullSmallProfileConstant (d : ℕ) : ℝ :=
  90*5^(d-2)*(2*(d : ℝ)+2)

/-- The actual coefficient factor at the source cutoff has its uniform
low/high-gamma power, with no spatial-center dependence. -/
theorem k4_cutoff_factor_le (d : ℕ) {L δ γ : ℝ} (hL : 1 ≤ L)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    2*((d : ℝ)*(L*(δ⁻¹*L^(-2*γ)))/k4CoefficientCut L γ)+2 ≤
      (2*(d : ℝ)+2)*δ⁻¹*L^(1-γ-min γ (1-γ)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hD : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hprod : L*(δ⁻¹*L^(-2*γ))=δ⁻¹*L^(1-2*γ) := by
    calc
      _ = δ⁻¹*(L^(1 : ℝ)*L^(-2*γ)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hLp]; congr 2; ring
  by_cases hh : γ ≤ 1/2
  · have hmin : min γ (1-γ)=γ := min_eq_left (by linarith only [hh])
    have he : 1-γ-γ=1-2*γ := by ring
    rw [k4CoefficientCut,ite_eq_left hh,hmin,he,hprod,div_one]
    have hP : 1 ≤ L^(1-2*γ) := Real.one_le_rpow hL (by linarith only [hh])
    have hA : 1 ≤ δ⁻¹*L^(1-2*γ) := one_le_mul_of_one_le_of_one_le hD hP
    nlinarith only [hA]
  · have hmin : min γ (1-γ)=1-γ := min_eq_right (by linarith only [hh])
    have he : 1-γ-(1-γ)=0 := by ring
    rw [k4CoefficientCut,ite_eq_right hh,hmin,he,Real.rpow_zero,mul_one,hprod]
    have hpow : L^(1-2*γ) ≠ 0 := (Real.rpow_pos_of_pos hLp _).ne'
    have hid : (d : ℝ)*(δ⁻¹*L^(1-2*γ))/L^(1-2*γ) = (d : ℝ)*δ⁻¹ := by field_simp [hpow]
    rw [hid]
    nlinarith only [hD]

/-- The actual small-sphere profile above the source coefficient cutoff
leaves a strict 1.05 gamma-zero saving in the remaining-label dimension. -/
theorem k4_full_small_profile_le (d : ℕ) (hd : 2 ≤ d) {L δ γ : ℝ}
    (hL : 1 ≤ L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hγ : 0 < γ) (hγ1 : γ < 1) :
    k4SmallFiberProfile d L (δ⁻¹*L^(-2*γ)) (k4CoefficientCut L γ) (L^(1-min γ (1-γ)/10)) ≤
      k4FullSmallProfileConstant d*(δ⁻¹)^2*
        L^((d : ℝ)-γ-(21 : ℝ)/20*min γ (1-γ)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hD0 : 0 < δ⁻¹ := inv_pos.mpr hδ.1
  have hcut : 0 < k4CoefficientCut L γ := k4_coefficient_cut_pos hLp
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := by positivity
  have hb : (4*L+1)^(d-2) ≤ (5 : ℝ)^(d-2)*L^(d-2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) _
  have hq := k4_cutoff_factor_le d (γ := γ) hL hδ
  have hz := k4_small_height_factor_le hL hδ hγ hγ1
  have hq0 : 0 ≤ 2*((d : ℝ)*(L*(δ⁻¹*L^(-2*γ)))/k4CoefficientCut L γ)+2 := by positivity
  have hz0 : 0 ≤ 2*Real.sqrt (2*(L^2*(2*(δ⁻¹*L^(-2*γ)))+4*(L*L^(1-min γ (1-γ)/10))+1))+2 := by positivity
  have hh := mul_le_mul (mul_le_mul hb hq hq0 (by positivity)) hz hz0 (by positivity)
  have hh' := mul_le_mul_of_nonneg_right hh (by norm_num : (0 : ℝ)≤9)
  have hm : ((d-2 : ℕ) : ℝ)=(d : ℝ)-2 := by rw [Nat.cast_sub hd]; norm_num
  have hp : L^(d-2)*L^(1-γ-min γ (1-γ))*L^(1-min γ (1-γ)/20) =
      L^((d : ℝ)-γ-(21 : ℝ)/20*min γ (1-γ)) := by
    rw [← Real.rpow_natCast L (d-2),← Real.rpow_add hLp,← Real.rpow_add hLp,hm]
    congr 1
    ring
  unfold k4SmallFiberProfile
  calc
    _ = (((4*L+1)^(d-2)*(2*((d : ℝ)*(L*(δ⁻¹*L^(-2*γ)))/k4CoefficientCut L γ)+2))*
      (2*Real.sqrt (2*(L^2*(2*(δ⁻¹*L^(-2*γ)))+4*(L*L^(1-min γ (1-γ)/10))+1))+2))*9 := by ring
    _ ≤ (((5 : ℝ)^(d-2)*L^(d-2))*((2*(d : ℝ)+2)*δ⁻¹*L^(1-γ-min γ (1-γ))))*
      (10*δ⁻¹*L^(1-min γ (1-γ)/20))*9 := hh'
    _ = (90*5^(d-2)*(2*(d : ℝ)+2))*(δ⁻¹)^2*
        (L^(d-2)*L^(1-γ-min γ (1-γ))*L^(1-min γ (1-γ)/20)) := by ring
    _ = _ := by rw [hp]; rfl

end WaveTurbulence.MoleProp
