/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.InterpolationMargins
public import WaveTurbulence.Foundations.Sumint.ExponentMargins

/-!
# Numerical smallness conditions used to assemble the source proposition

These are only inequalities in d, gamma and eta. They will be obtained
uniformly for all positive eta below an explicit threshold, before any
step count or delta is chosen.
-/

public section
namespace WaveTurbulence.Sumint

/-- Numerical parameter margins for the actual kernel and exact restriction estimate. -/
structure SumintSmallness (d : ℕ) (γ η : ℝ) : Prop where
  eta_pos : 0 < η
  eta_base : η ≤ gammaBase γ
  eta_small : η ≤ 1/24
  gamma_eta : γ+η ≤ 1
  sqrt_base : Real.sqrt η ≤ gammaBase γ/8
  beta_linear : partitionExponent η/2 < 2*γ
  beta_pair : partitionExponent η/2 < 2*((d:ℝ)-1)*(1-γ)-η
  beta_normal : partitionExponent η < 20*γ
  beta_high : 1/2 < γ → partitionExponent η/20 < min (2*γ-1) (1-γ)
  eight_lt : 8*η^8 < 1
  twentyfour_le : 24*η^8 ≤ 1
  sqrt_forty : 40*Real.sqrt η ≤ 1
  half_loss : 12*Real.sqrt η+168*(d:ℝ)*η ≤ 1/2
  square_gain : η^2 ≤ gammaBase γ/8
  parameter_power : 2*η^8 ≤ η^6

/-- The partition exponent is strictly positive at every positive source eta. -/
theorem partitionExponent_pos {η : ℝ} (hη : 0 < η) : 0 < partitionExponent η :=
  mul_pos (pow_pos hη _) (Real.sqrt_pos.mpr hη)

/-- Below one, the actual partition exponent is at most eta. -/
theorem partitionExponent_le_eta {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    partitionExponent η ≤ η := by
  have hp : η^7 ≤ η := by
    simpa only [pow_one] using pow_le_pow_of_le_one hη hη1 (by norm_num : 1 ≤ 7)
  have hs : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr hη1
  exact (mul_le_mul_of_nonneg_left hs (pow_nonneg hη _)).trans_eq (mul_one _) |>.trans hp

end WaveTurbulence.Sumint
