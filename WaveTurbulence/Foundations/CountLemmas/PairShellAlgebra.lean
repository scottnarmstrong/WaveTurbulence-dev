/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Polynomial radial profiles in the elementary pair-strip bound -/

public section
namespace WaveTurbulence.CountLemmas

/-- At scales above one lattice spacing, the two box counts have an exact
polynomial radial profile. Its two exponents are positive in dimension ≥3. -/
theorem pair_shell_profile_bound (n : ℕ) (hn : 1 ≤ n) {L R U T : ℝ}
    (hL : 1 ≤ L) (hR : 0 < R) (hLR : 1 ≤ L*R) (hU : 0 ≤ U) (hT : 0 ≤ T) :
    (2*(L*R)+1)^n*U*((2*L+1)^n*(T/R+1)) ≤
      (3^n*L^n)^2*U*(R^n+T*R^(n-1)) := by
  have hx : (2*(L*R)+1)^n ≤ (3 : ℝ)^n*L^n*R^n := by
    calc
      _ ≤ (3*(L*R))^n := pow_le_pow_left₀ (by positivity) (by linarith only [hLR]) n
      _ = _ := by rw [mul_pow,mul_pow]; ring
  have hy : (2*L+1)^n ≤ (3 : ℝ)^n*L^n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) n
  have hprof : R^n*(T/R+1) = R^n+T*R^(n-1) := by
    have hp : R^n = R^(n-1)*R := by rw [← pow_succ,Nat.sub_add_cancel hn]
    rw [hp]
    field_simp
    ring
  calc
    _ ≤ ((3 : ℝ)^n*L^n*R^n)*U*(((3 : ℝ)^n*L^n)*(T/R+1)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hx hU)
        (mul_le_mul_of_nonneg_right hy (by positivity)) (by positivity) (by positivity)
    _ = (3^n*L^n)^2*U*(R^n*(T/R+1)) := by ring
    _ = _ := by rw [hprof]

end WaveTurbulence.CountLemmas
