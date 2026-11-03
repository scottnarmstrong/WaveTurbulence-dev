/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Explicit coefficient-budget optimization for estcross

This is scalar algebra applied to the proved harmonic-weight count, with
all coefficient and logarithm bounds made explicit.
-/

public section

namespace WaveTurbulence.Counting

/-- Replace the actual short-coefficient budget by its density-scale bound
and the harmonic logarithm by `1 + log L`. -/
theorem short_relation_count_bound {k M : ℕ} {L rho theta : ℝ}
    (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hbudget : (M:ℝ) ≤ 10*((3:ℝ)^k*theta)) (hML : (M:ℝ) ≤ L) :
    1296*(2*L+1)^k*rho^2*(M:ℝ)^2*(1+Real.log M)^2 ≤
      129600*((3:ℝ)^k)^3*L^k*rho^2*theta^2*(1+Real.log L)^2 := by
  have hbase : (2*L+1)^k ≤ (3*L)^k :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hL]) k
  have hMsq := pow_le_pow_left₀ (Nat.cast_nonneg M) hbudget 2
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hlog : 1+Real.log (M:ℝ) ≤ 1+Real.log L :=
    add_le_add le_rfl (Real.log_le_log (lt_of_lt_of_le zero_lt_one hMr) hML)
  have hlog0 : 0 ≤ 1+Real.log (M:ℝ) := by
    have hh := Real.log_nonneg hMr
    linarith only [hh]
  have hlogsq := pow_le_pow_left₀ hlog0 hlog 2
  have hp := mul_le_mul hbase hMsq (sq_nonneg (M:ℝ)) (by positivity : 0 ≤ (3*L)^k)
  have hp' := mul_le_mul hp hlogsq (sq_nonneg (1+Real.log (M:ℝ)))
    (by positivity : 0 ≤ (3*L)^k*(10*((3:ℝ)^k*theta))^2)
  have hm := mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ 1296*rho^2)
  calc
    _ = (1296*rho^2)*(((2*L+1)^k*(M:ℝ)^2)*(1+Real.log M)^2) := by ring
    _ ≤ (1296*rho^2)*(((3*L)^k*(10*((3:ℝ)^k*theta))^2)*(1+Real.log L)^2) := hm
    _ = _ := by rw [mul_pow]; ring

end WaveTurbulence.Counting
