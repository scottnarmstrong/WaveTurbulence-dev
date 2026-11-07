/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountProfileBoxes
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountSmallPower
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountMonomials
import Mathlib.Tactic

/-! # Power form of the actual localized small-sphere K4 profiles

The exact three positive coefficient-radius powers are retained. The
only logarithm is the actual translated harmonic factor, uniform over
source blocks and absorbed after finite geometric summation.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

/-- Literal source profiles at M=L^(1−γ₀/10) have a uniform three-term
power majorant. No estimate on an abstract counting problem is assumed. -/
theorem k4_small_block_power_le (d : ℕ) (hd : 3 ≤ d) {L R δ γ : ℝ}
    (hL : 1 ≤ L) (hR : 0 < R) (hLR : 1 ≤ L*R)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hγ : 0 < γ) (hγ1 : γ < 1) :
    k4BaseLocalProfile d L (δ⁻¹*L^(-2*γ)) R*
      k4SmallFiberProfile d L (δ⁻¹*L^(-2*γ)) (R/2) (L^(1-min γ (1-γ)/10)) ≤
    (10*k4BlockBoxConstant d)*(3+2*Real.log (⌈2*(L*R)+1⌉₊ : ℝ))*(δ⁻¹)^3*
      (L^(3*(d : ℝ)-4*γ-min γ (1-γ)/20)*R^(d-2)+
       L^(3*(d : ℝ)-2*γ-1-min γ (1-γ)/20)*R^(d-1)+
       L^(3*(d : ℝ)-2-min γ (1-γ)/20)*R^d) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hD : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hD0 : 0 ≤ δ⁻¹ := zero_le_one.trans hD
  let g := min γ (1-γ)
  let e := 1-g/20
  let τ := δ⁻¹*L^(-2*γ)
  let H := 3+2*Real.log (⌈2*(L*R)+1⌉₊ : ℝ)
  let N := 3*d-4
  have hτ : 0 ≤ τ := mul_nonneg hD0 (Real.rpow_nonneg hLp.le _)
  have hH0 : 0 ≤ H := zero_le_one.trans (k4_harmonic_factor_one_le hLp.le hR.le)
  have hK : 0 ≤ k4BlockBoxConstant d := by unfold k4BlockBoxConstant; positivity
  have hsum0 : 0 ≤ τ^2*L^3*R^(d-2)+τ*L^2*R^(d-1)+L*R^d := by positivity
  have hheight : k4SphereHeight L τ (L^(1-g/10)) ≤ 10*δ⁻¹*L^e :=
    k4_small_height_factor_le hL hδ hγ hγ1
  have hboxes := k4_block_profiles_box_le d hd hL hR hLR hτ (M := L^(1-g/10))
  have hm := mul_le_mul_of_nonneg_left hheight (mul_nonneg hK hH0)
  have hm' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ L^N)) hsum0
  have he : (k4BlockBoxConstant d*H*(10*δ⁻¹*L^e))*L^N*
      (τ^2*L^3*R^(d-2)+τ*L^2*R^(d-1)+L*R^d) =
    (10*k4BlockBoxConstant d*H)*
      ((δ⁻¹*L^N*L^e*(τ^2*L^3))*R^(d-2)+
       (δ⁻¹*L^N*L^e*(τ*L^2))*R^(d-1)+
       (δ⁻¹*L^N*L^e*L)*R^d) := by ring
  have hbound := hboxes.trans hm'
  rw [he] at hbound
  have hN : (N : ℝ)=3*(d : ℝ)-4 := by
    dsimp only [N]
    rw [Nat.cast_sub (by omega : 4 ≤ 3*d),Nat.cast_mul]
    norm_num
  have he1 : (N : ℝ)+e+3-4*γ=3*(d : ℝ)-4*γ-g/20 := by rw [hN]; dsimp only [e]; ring
  have he2 : (N : ℝ)+e+2-2*γ=3*(d : ℝ)-2*γ-1-g/20 := by rw [hN]; dsimp only [e]; ring
  have he3 : (N : ℝ)+e+1=3*(d : ℝ)-2-g/20 := by rw [hN]; dsimp only [e]; ring
  have ht1 : δ⁻¹*L^N*L^e*(τ^2*L^3) = (δ⁻¹)^3*L^(3*(d : ℝ)-4*γ-g/20) := by
    dsimp only [τ]
    rw [k4_tau_square_monomial N hLp,he1]
  have ht2 : δ⁻¹*L^N*L^e*(τ*L^2) = (δ⁻¹)^2*L^(3*(d : ℝ)-2*γ-1-g/20) := by
    dsimp only [τ]
    rw [k4_tau_linear_monomial N hLp,he2]
  have ht3 : δ⁻¹*L^N*L^e*L = δ⁻¹*L^(3*(d : ℝ)-2-g/20) := by
    rw [k4_tau_zero_monomial N hLp,he3]
  rw [ht1,ht2,ht3] at hbound
  have hD2 : (δ⁻¹)^2 ≤ (δ⁻¹)^3 := pow_le_pow_right₀ hD (by norm_num : (2 : ℕ)≤3)
  have hD1 : δ⁻¹ ≤ (δ⁻¹)^3 := by simpa only [pow_one] using pow_le_pow_right₀ hD (by norm_num : (1 : ℕ)≤3)
  have h2 := mul_le_mul_of_nonneg_right hD2
    (by positivity : 0 ≤ L^(3*(d : ℝ)-2*γ-1-g/20)*R^(d-1))
  have h3 := mul_le_mul_of_nonneg_right hD1
    (by positivity : 0 ≤ L^(3*(d : ℝ)-2-g/20)*R^d)
  have hrest : (δ⁻¹)^3*L^(3*(d : ℝ)-4*γ-g/20)*R^(d-2)+
      (δ⁻¹)^2*L^(3*(d : ℝ)-2*γ-1-g/20)*R^(d-1)+
      δ⁻¹*L^(3*(d : ℝ)-2-g/20)*R^d ≤
      (δ⁻¹)^3*(L^(3*(d : ℝ)-4*γ-g/20)*R^(d-2)+
        L^(3*(d : ℝ)-2*γ-1-g/20)*R^(d-1)+L^(3*(d : ℝ)-2-g/20)*R^d) := by
    nlinarith only [h2,h3]
  have hfinal := mul_le_mul_of_nonneg_left hrest (by positivity : 0 ≤ 10*k4BlockBoxConstant d*H)
  exact hbound.trans (by simpa only [mul_assoc] using hfinal)

end WaveTurbulence.MoleProp
