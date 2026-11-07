/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Radial profile without an independent strip -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

theorem appb_small_gap_shell_profile (d : ℕ) (hd : 1 ≤ d) {L R T : ℝ}
    (hL : 1 ≤ L) (hR : 0 < R) (hLR : 1 ≤ L*R) (hT : 0 ≤ T) :
    (2*(L*R)+1)^d*((2*L+1)^(d-1)*(T/R+1)) ≤
      (3^d*L^d)*(3^(d-1)*L^(d-1))*(R^d+T*R^(d-1)) := by
  have hx : (2*(L*R)+1)^d ≤ (3 : ℝ)^d*L^d*R^d := by
    calc
      _ ≤ (3*(L*R))^d := pow_le_pow_left₀ (by positivity) (by linarith only [hLR]) d
      _ = _ := by rw [mul_pow,mul_pow]; ring
  have hy : (2*L+1)^(d-1) ≤ (3 : ℝ)^(d-1)*L^(d-1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) _
  have hprof : R^d*(T/R+1) = R^d+T*R^(d-1) := by
    have hp : R^d = R^(d-1)*R := by rw [← pow_succ,Nat.sub_add_cancel hd]
    rw [hp]
    field_simp
    ring
  calc
    _ ≤ ((3 : ℝ)^d*L^d*R^d)*(((3 : ℝ)^(d-1)*L^(d-1))*(T/R+1)) :=
      mul_le_mul hx (mul_le_mul_of_nonneg_right hy (by positivity)) (by positivity) (by positivity)
    _ = (3^d*L^d)*(3^(d-1)*L^(d-1))*(R^d*(T/R+1)) := by ring
    _ = _ := by rw [hprof]

end WaveTurbulence.Mole
