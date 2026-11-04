/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.DraftNormInterpolation
public import WaveTurbulence.Foundations.Sumint.SourceScalePowers

/-!
# Exact numerical endpoint interpolation and coefficient absorption

The two endpoint estimates use one common exponential-in-input-count
constant. Their shared mass scale therefore survives interpolation
unchanged, while the positive lattice loss and negative discrepancy
gain acquire exactly their interpolation weights.
-/

public section
open ENNReal
namespace WaveTurbulence.Sumint

/-- A single real coefficient is absorbed by a common constant to any positive input count. -/
theorem coefficient_mul_pow_le_common {C G H : ℝ} (hG : 0 ≤ G) (hGH : G ≤ H)
    {m : ℕ} (hm : 0 < m) : C*G^m ≤ (max 1 C*H)^m := by
  have hK : 1 ≤ max 1 C := le_max_left _ _
  have hC : C ≤ (max 1 C)^m := (le_max_right _ _).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hK (Nat.succ_le_iff.mpr hm))
  have hp : G^m ≤ H^m := pow_le_pow_left₀ hG hGH _
  calc
    _ ≤ (max 1 C)^m*H^m := mul_le_mul hC hp (pow_nonneg hG _) (pow_nonneg (zero_le_one.trans hK) _)
    _ = _ := (mul_pow _ _ _).symm

/-- Exact geometric interpolation of two positive source power budgets with their shared mass scale. -/
theorem geometric_endpoint_budget {A L E P Q a : ℝ} (hA : 0 < A) (hL : 0 < L) :
    (ENNReal.ofReal (A*L^(E+P)))^a * (ENNReal.ofReal (A*L^(E-Q)))^(1-a) =
      ENNReal.ofReal (A*L^(E+a*P-(1-a)*Q)) := by
  have hleft : 0 < A*L^(E+P) := mul_pos hA (Real.rpow_pos_of_pos hL _)
  have hright : 0 < A*L^(E-Q) := mul_pos hA (Real.rpow_pos_of_pos hL _)
  rw [ENNReal.ofReal_rpow_of_pos hleft,ENNReal.ofReal_rpow_of_pos hright,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hleft.le _)]
  congr 1
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hL.le _),
    Real.mul_rpow hA.le (Real.rpow_nonneg hL.le _),← Real.rpow_mul hL.le,← Real.rpow_mul hL.le]
  calc
    _ = (A^a*A^(1-a))*(L^((E+P)*a)*L^((E-Q)*(1-a))) := by ring
    _ = A*L^((E+P)*a+(E-Q)*(1-a)) := by
      rw [← Real.rpow_add hA,← Real.rpow_add hL,show a+(1-a) = 1 by ring,Real.rpow_one]
    _ = _ := by congr 2; ring

end WaveTurbulence.Sumint
