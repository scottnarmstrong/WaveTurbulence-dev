/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountBlocks
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountBlockAlgebra
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountLog
import Mathlib.Tactic

/-! # Actual K4 block profiles retain three summable radius powers

Only translated-box arithmetic is used here. The true sphere height is
retained rather than supplied as a conclusion-shaped bound.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

noncomputable def k4SphereHeight (L τ M : ℝ) : ℝ :=
  2*Real.sqrt (2*(L^2*(2*τ)+4*(L*M)+1))+2

noncomputable def k4BlockBoxConstant (d : ℕ) : ℝ :=
  (d : ℝ)*3^(2*(d-1))*5^(d-2)*9*(16*(d : ℝ)+8)

/-- Two actual translated boxes keep the radius-volume factor explicitly. -/
theorem k4_base_box_product_le (n : ℕ) {L R : ℝ} (hL : 1 ≤ L) (hR : 0 ≤ R) (hLR : 1 ≤ L*R) :
    (2*(L*R)+1)^n*(2*L+1)^n ≤ 3^(2*n)*L^(2*n)*R^n := by
  have hx : (2*(L*R)+1)^n ≤ (3 : ℝ)^n*L^n*R^n := by
    calc
      _ ≤ (3*(L*R))^n := pow_le_pow_left₀ (by positivity) (by linarith only [hLR]) n
      _ = _ := by rw [mul_pow,mul_pow]; ring
  have hy : (2*L+1)^n ≤ (3 : ℝ)^n*L^n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) n
  have hh := mul_le_mul hx hy (by positivity : 0 ≤ (2*L+1)^n) (by positivity : 0 ≤ 3^n*L^n*R^n)
  convert hh using 1 <;> rw [show 2*n=n+n by omega,pow_add,pow_add] <;> ring

/-- The source profiles, not abstract count premises, have a polynomial
radius majorant with positive exponents in dimension at least three. -/
theorem k4_block_profiles_box_le (d : ℕ) (hd : 3 ≤ d) {L R τ M : ℝ}
    (hL : 1 ≤ L) (hR : 0 < R) (hLR : 1 ≤ L*R) (hτ : 0 ≤ τ) :
    k4BaseLocalProfile d L τ R*k4SmallFiberProfile d L τ (R/2) M ≤
      k4BlockBoxConstant d*(3+2*Real.log (⌈2*(L*R)+1⌉₊ : ℝ))*k4SphereHeight L τ M*L^(3*d-4)*
        (τ^2*L^3*R^(d-2)+τ*L^2*R^(d-1)+L*R^d) := by
  let n := d-1
  let m := d-2
  let H := 3+2*Real.log (⌈2*(L*R)+1⌉₊ : ℝ)
  let Z := k4SphereHeight L τ M
  let Q := 4*(d : ℝ)*L*τ/R+2
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hH : 1 ≤ H := k4_harmonic_factor_one_le hLp.le hR.le
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hZ : 0 ≤ Z := by dsimp only [Z,k4SphereHeight]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hbox := k4_base_box_product_le n hL hR.le hLR
  have htail : τ*L^2*H+(2*(L*R)+1) ≤ τ*L^2*H+3*L*R := by linarith only [hLR]
  have hG : k4BaseLocalProfile d L τ R ≤
      (d : ℝ)*(3^(2*n)*L^(2*n)*R^n)*(τ*L^2*H+3*L*R) := by
    have hb := mul_le_mul_of_nonneg_left hbox hd0
    have hh := mul_le_mul hb htail (by positivity : 0 ≤ τ*L^2*H+(2*(L*R)+1)) (by positivity : 0 ≤ (d : ℝ)*(3^(2*n)*L^(2*n)*R^n))
    simpa only [k4BaseLocalProfile,n,H,mul_assoc] using hh
  have houter : (4*L+1)^m ≤ (5 : ℝ)^m*L^m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) m
  have hcoef : 2*((d : ℝ)*(L*τ)/(R/2))+2=Q := by dsimp only [Q]; field_simp [hR.ne'] <;> ring
  have hF : k4SmallFiberProfile d L τ (R/2) M ≤ ((5 : ℝ)^m*L^m)*Q*Z*9 := by
    unfold k4SmallFiberProfile
    rw [hcoef]
    simpa only [m,Z,k4SphereHeight,mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right houter hQ) hZ) (by norm_num : (0 : ℝ)≤9)
  have hF0 : 0 ≤ k4SmallFiberProfile d L τ (R/2) M := by unfold k4SmallFiberProfile; positivity
  have hG0 : 0 ≤ (d : ℝ)*(3^(2*n)*L^(2*n)*R^n)*(τ*L^2*H+3*L*R) := by positivity
  have hh := mul_le_mul hG hF hF0 hG0
  let O := (d : ℝ)*3^(2*n)*5^m*9*Z*L^(2*n+m)
  have hO : 0 ≤ O := by dsimp only [O]; positivity
  have he : ((d : ℝ)*(3^(2*n)*L^(2*n)*R^n)*(τ*L^2*H+3*L*R))*(((5 : ℝ)^m*L^m)*Q*Z*9) =
      O*(R^n*(τ*L^2*H+3*L*R)*(4*(d : ℝ)*L*τ/R+2)) := by
    dsimp only [O,Q]
    rw [pow_add]
    ring
  rw [he] at hh
  have hp := mul_le_mul_of_nonneg_left
    (k4_block_radial_profile n (by dsimp only [n]; omega) hd1 hLp.le hR hτ hH) hO
  apply hh.trans
  apply hp.trans_eq
  have hn : n-1=d-2 := by dsimp only [n]; omega
  have hn1 : n+1=d := by dsimp only [n]; omega
  have hdim : 2*n+m=3*d-4 := by dsimp only [n,m]; omega
  dsimp only [O,k4BlockBoxConstant,Z,H]
  rw [hn,hn1,hdim]
  dsimp only [n,m]
  ring

end WaveTurbulence.MoleProp
