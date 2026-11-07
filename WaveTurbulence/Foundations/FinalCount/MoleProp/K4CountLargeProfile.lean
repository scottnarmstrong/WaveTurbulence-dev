/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountFibers
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountLargePower
import Mathlib.Tactic

/-! # Power majorant for the actual large-radius K4 fiber profile

The source threshold leaves a full tenth gamma-zero beyond the base
saving. All numeric constants depend only on the fixed dimension.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

noncomputable def k4LargeProfileConstant (d : ℕ) : ℝ :=
  (d : ℝ)*640000*5^(d-2)*(2+48*(d : ℝ))

/-- The literal annulus profile at the source physical radius threshold
has the required stronger planar power, uniformly in every fixed δ. -/
theorem k4_large_profile_le (d : ℕ) (hd : 3 ≤ d) {L δ γ : ℝ}
    (hL : 1 ≤ L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hγ : 0 < γ) (hγ1 : γ < 1) :
    k4LargeFiberProfile d L (δ⁻¹*L^(-2*γ)) (L^(1-min γ (1-γ)/10)) ≤
      k4LargeProfileConstant d*(δ⁻¹)^2*
        L^(((d : ℝ)-2)+(max 1 (2-2*γ)-min γ (1-γ)/10)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hdR
  have h2d : (1 : ℝ) ≤ 2*(d : ℝ) := by linarith only [hdR]
  have hD : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hD0 : 0 < δ⁻¹ := zero_lt_one.trans_le hD
  have hDsq : δ⁻¹ ≤ (δ⁻¹)^2 := by nlinarith only [hD]
  let g := min γ (1-γ)
  let t := L^(1-γ)
  let W := L^2*(2*(δ⁻¹*L^(-2*γ)))
  let Q := ((L*L^(1-g/10))/(d : ℝ))/2
  let p := max 1 (2-2*γ)-g/10
  have ht : 0 < t := Real.rpow_pos_of_pos hLp _
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have ht2 : t^2=L^(2-2*γ) := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast hLp.le]
    congr 1
    ring
  have ht3 : t^3=L^(3-3*γ) := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast hLp.le]
    congr 1
    ring
  have hW : W=2*δ⁻¹*t^2 := by
    dsimp only [W]
    rw [ht2]
    have he : L^2*L^(-2*γ)=L^(2-2*γ) := by
      rw [← Real.rpow_two,← Real.rpow_add hLp]
      congr 1
      ring
    rw [← he]
    ring
  have hW0 : 0 < W := by rw [hW]; positivity
  have hQform : Q=L^(2-g/10)/(2*(d : ℝ)) := by
    have he : L*L^(1-g/10)=L^(2-g/10) := by
      calc
        _ = L^(1 : ℝ)*L^(1-g/10) := by rw [Real.rpow_one]
        _ = L^((1 : ℝ)+(1-g/10)) := (Real.rpow_add hLp _ _).symm
        _ = _ := by congr 1; ring
    dsimp only [Q]
    rw [he]
    field_simp [hd0.ne'] <;> ring
  have hIQ : Q⁻¹=(2*(d : ℝ))*L^(-(2-g/10)) := by
    rw [hQform,inv_div,Real.rpow_neg hLp.le]
    rfl
  have hSQ : Real.sqrt W ≤ 2*δ⁻¹*L^(1-γ) := by
    rw [hW]
    exact k4_sqrt_energy_bound hD ht.le
  have hThree : W^((3 : ℝ)/2) ≤ 4*(δ⁻¹)^2*L^(3-3*γ) := by
    rw [hW,← ht3]
    exact k4_energy_three_halves_bound hD ht
  have hCubert : Q^(-((1 : ℝ)/3)) ≤ (2*(d : ℝ))*L^(-(2-g/10)/3) := by
    rw [hQform]
    exact k4_radius_inverse_cuberoot hLp h2d
  have hterm1 : Real.sqrt W ≤ 2*(δ⁻¹)^2*L^(1-γ) :=
    hSQ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDsq (by norm_num)) (Real.rpow_nonneg hLp.le _))
  have hterm2 : (4*L)*W^((3 : ℝ)/2)/Q ≤ 32*(d : ℝ)*(δ⁻¹)^2*L^(2-3*γ+g/10) := by
    have hh := mul_le_mul_of_nonneg_left hThree (by positivity : 0 ≤ 4*L)
    have hh' := div_le_div_of_nonneg_right hh hQ.le
    apply hh'.trans_eq
    rw [div_eq_mul_inv,hIQ]
    calc
      _ = (32*(d : ℝ)*(δ⁻¹)^2)*(L^(1 : ℝ)*L^(3-3*γ)*L^(-(2-g/10))) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hLp,← Real.rpow_add hLp]; congr 2; ring
  have hterm3 : (4*L)*Real.sqrt W*Q^(-((1 : ℝ)/3)) ≤
      16*(d : ℝ)*(δ⁻¹)^2*L^((4 : ℝ)/3-γ+g/30) := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hSQ (by positivity : 0 ≤ 4*L)) hCubert
      (Real.rpow_nonneg hQ.le _) (by positivity : 0 ≤ (4*L)*(2*δ⁻¹*L^(1-γ)))
    have he : ((4*L)*(2*δ⁻¹*L^(1-γ)))*((2*(d : ℝ))*L^(-(2-g/10)/3)) =
        16*(d : ℝ)*δ⁻¹*L^((4 : ℝ)/3-γ+g/30) := by
      calc
        _ = (16*(d : ℝ)*δ⁻¹)*(L^(1 : ℝ)*L^(1-γ)*L^(-(2-g/10)/3)) := by rw [Real.rpow_one]; ring
        _ = _ := by rw [← Real.rpow_add hLp,← Real.rpow_add hLp]; congr 2; ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDsq (by positivity : 0 ≤ 16*(d : ℝ))) (Real.rpow_nonneg hLp.le _))
  obtain ⟨he1,he2,he3⟩ := k4_large_radius_exponents hγ hγ1
  have h1 : Real.sqrt W ≤ 2*(δ⁻¹)^2*L^p := hterm1.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL he1) (by positivity))
  have h2 : (4*L)*W^((3 : ℝ)/2)/Q ≤ 32*(d : ℝ)*(δ⁻¹)^2*L^p := hterm2.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL he2) (by positivity))
  have h3 : (4*L)*Real.sqrt W*Q^(-((1 : ℝ)/3)) ≤ 16*(d : ℝ)*(δ⁻¹)^2*L^p := hterm3.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL he3) (by positivity))
  have hsum : Real.sqrt W+(4*L)*W^((3 : ℝ)/2)/Q+(4*L)*Real.sqrt W*Q^(-((1 : ℝ)/3)) ≤
      (2+48*(d : ℝ))*(δ⁻¹)^2*L^p := by nlinarith only [h1,h2,h3]
  have hb : (4*L+1)^(d-2) ≤ (5 : ℝ)^(d-2)*L^(d-2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) _
  have hsum0 : 0 ≤ Real.sqrt W+(4*L)*W^((3 : ℝ)/2)/Q+(4*L)*Real.sqrt W*Q^(-((1 : ℝ)/3)) := by positivity
  have hh := mul_le_mul hb hsum hsum0 (by positivity : 0 ≤ (5 : ℝ)^(d-2)*L^(d-2))
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (d : ℝ)*640000)
  have hm : ((d-2 : ℕ) : ℝ)=(d : ℝ)-2 := by rw [Nat.cast_sub (by omega : 2 ≤ d)]; norm_num
  have hpow : L^(d-2)*L^p = L^(((d : ℝ)-2)+p) := by
    rw [← Real.rpow_natCast L (d-2),← Real.rpow_add hLp,hm]
  unfold k4LargeFiberProfile
  change (d : ℝ)*((4*L+1)^(d-2)*(640000*(Real.sqrt W+(4*L)*W^((3 : ℝ)/2)/Q+
    (4*L)*Real.sqrt W*Q^(-((1 : ℝ)/3))))) ≤ _
  convert hh' using 1
  · ring
  · dsimp only [k4LargeProfileConstant,p,g]
    rw [← hpow]
    ring

end WaveTurbulence.MoleProp
