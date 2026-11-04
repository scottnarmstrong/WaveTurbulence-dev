/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ProductPowerEnvelopes

/-!
# Enlarging local constants and delta costs to the input-arity budget

For C at least one and delta at most one, both the constant power and
the reciprocal-delta power increase monotonically with their budgets.
This accounts for the unused half-power of delta in a bad block.
-/

public section

open ENNReal

namespace WaveTurbulence.Sumint

/-- Smaller local constant and delta costs fit into a larger arity budget. -/
theorem local_power_budget_mono {C δ L q e : ℝ} {a n : ℕ}
    (hC : 1 ≤ C) (hδ : δ ∈ Set.Ioc (0:ℝ) 1) (hL : 0 < L)
    (ha : a ≤ n) (hq : q ≤ (n:ℝ)/2) :
    C^a*δ^(-q)*L^e ≤ C^n*δ^(-(n:ℝ)/2)*L^e := by
  have hc : C^a ≤ C^n := pow_le_pow_right₀ hC ha
  have hd : δ^(-q) ≤ δ^(-(n:ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_ge hδ.1 hδ.2 (by linarith only [hq])
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hc hd (Real.rpow_nonneg hδ.1.le _) (pow_nonneg (zero_le_one.trans hC) _))
    (Real.rpow_nonneg hL.le _)

/-- A pure lattice-power gain fits any nonnegative arity's constant/delta budget. -/
theorem lattice_power_le_local_budget {C δ L e : ℝ} (n : ℕ)
    (hC : 1 ≤ C) (hδ : δ ∈ Set.Ioc (0:ℝ) 1) (hL : 0 < L) :
    L^e ≤ C^n*δ^(-(n:ℝ)/2)*L^e := by
  have hb := local_power_budget_mono (q := 0) (e := e) hC hδ hL (Nat.zero_le n)
    (by positivity : (0:ℝ) ≤ (n:ℝ)/2)
  simpa only [pow_zero,neg_zero,Real.rpow_zero,one_mul] using hb

/-- Two local arity budgets multiply with exactly added arities and lattice exponents. -/
theorem mul_local_power_envelopes {F G : ℝ≥0∞} {C δ L e f : ℝ} (a b : ℕ)
    (hC : 0 ≤ C) (hδ : 0 < δ) (hL : 0 < L)
    (hF : F ≤ ENNReal.ofReal (C^a*δ^(-(a:ℝ)/2)*L^e))
    (hG : G ≤ ENNReal.ofReal (C^b*δ^(-(b:ℝ)/2)*L^f)) :
    F*G ≤ ENNReal.ofReal (C^(a+b)*δ^(-((a+b:ℕ):ℝ)/2)*L^(e+f)) := by
  have hd : δ^(-(a:ℝ)/2)*δ^(-(b:ℝ)/2) = δ^(-((a+b:ℕ):ℝ)/2) := by
    rw [← Real.rpow_add hδ]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ENNReal.ofReal (C^a*δ^(-(a:ℝ)/2)*L^e)*ENNReal.ofReal (C^b*δ^(-(b:ℝ)/2)*L^f) := mul_le_mul' hF hG
    _ = ENNReal.ofReal ((C^a*C^b)*(δ^(-(a:ℝ)/2)*δ^(-(b:ℝ)/2))*(L^e*L^f)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (pow_nonneg hC _) (Real.rpow_nonneg hδ.le _))
        (Real.rpow_nonneg hL.le _))]
      congr 1
      ring
    _ = _ := by rw [← pow_add,hd,← Real.rpow_add hL]

end WaveTurbulence.Sumint
