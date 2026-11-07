/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountPowers
import Mathlib.Tactic

/-! # Scalar power bounds for the large-radius annulus branch

The actual annulus width is a squared physical tolerance times L².
These inequalities keep a uniform integer power of δ inverse.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

/-- A convenient uniform square-root bound with only one full inverse
small parameter; the spare half power is not hidden in a constant. -/
theorem k4_sqrt_energy_bound {D t : ℝ} (hD : 1 ≤ D) (ht : 0 ≤ t) :
    Real.sqrt (2*D*t^2) ≤ 2*D*t := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hcoef : 2*D ≤ 4*D^2 := by nlinarith only [hD]
  have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
  nlinarith only [hh]

/-- The three-halves width factor costs at most two full inverse small
parameters, by multiplying the proved square-root estimate by its width. -/
theorem k4_energy_three_halves_bound {D t : ℝ} (hD : 1 ≤ D) (ht : 0 < t) :
    (2*D*t^2)^((3 : ℝ)/2) ≤ 4*D^2*t^3 := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hW : 0 < 2*D*t^2 := by positivity
  have he : (2*D*t^2)^((3 : ℝ)/2) = (2*D*t^2)*Real.sqrt (2*D*t^2) := by
    calc
      _ = (2*D*t^2)^((1 : ℝ)+(1/2 : ℝ)) := by congr 1; norm_num
      _ = (2*D*t^2)^(1 : ℝ)*(2*D*t^2)^(1/2 : ℝ) := Real.rpow_add hW _ _
      _ = _ := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (k4_sqrt_energy_bound hD ht.le) hW.le
  convert hh using 1 <;> ring

/-- A denominator constant in the lower-radius bound costs at most its
first power after taking an inverse cube root. -/
theorem k4_radius_inverse_cuberoot {L D q : ℝ} (hL : 0 < L) (hD : 1 ≤ D) :
    (L^q/D)^(-((1 : ℝ)/3)) ≤ D*L^(-q/3) := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hQ : 0 < L^q/D := by positivity
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hQ.le _) (by positivity : 0 ≤ D*L^(-q/3))
    (by norm_num : (3 : ℕ)≠0)).mp
  have hleft : ((L^q/D)^(-((1 : ℝ)/3)))^3 = D/L^q := by
    rw [← Real.rpow_mul_natCast hQ.le]
    norm_num only [Nat.cast_ofNat]
    rw [Real.rpow_neg_one,inv_div]
  have hright : (D*L^(-q/3))^3 = D^3/L^q := by
    rw [mul_pow,← Real.rpow_mul_natCast hL.le]
    have he : L^((-q/3)*((3 : ℕ) : ℝ))=L^(-q) := by congr 1; norm_num <;> ring
    rw [he,Real.rpow_neg hL.le]
    rfl
  rw [hleft,hright]
  have hD3 : D ≤ D^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hD (by norm_num : (1 : ℕ)≤3)
  exact div_le_div_of_nonneg_right hD3 (Real.rpow_nonneg hL.le _)

end WaveTurbulence.MoleProp
