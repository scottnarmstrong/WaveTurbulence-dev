/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Regref.Inputs

/-!
# The order range `n ≤ N_{p+1}^4` is polylogarithmic (T (parameters2), L611–L612)

`R_𝔇 = ⌊(log L)^{40d}⌋`, `R_{p-1} = R_p^{(40d)^2}`, `N_p = R_p^{40d}` (T (parameters2)). With `log L ≥ 1`,
`R_p ≤ (log L)^{40d (1600d²)^{𝔇-p}}`, so every order `n ≤ N_{p+1}^4` satisfies `n ≤ (log L)^{A(d,𝔇)}` with
`A(d,𝔇) = 160d · 40d · (1600d²)^𝔇` (`le_logPow_ordExp`). This is the order range of the obligations RA1.
-/

@[expose] public section

open MeasureTheory Set

namespace WaveTurbulence.Regref

/-- The polylogarithmic order exponent `A(d, 𝔇) = 160d · 40d · (1600d²)^𝔇`. -/
def ordExp (d D : ℕ) : ℕ := 160 * d * (40 * d * (1600 * d ^ 2) ^ D)

theorem Rdown_le (P : WTParams) (hL : 0 ≤ Real.log P.L) (k : ℕ) :
    (P.Rdown k : ℝ) ≤ Real.log P.L ^ (40 * P.d * (1600 * P.d ^ 2) ^ k) := by
  induction k with
  | zero =>
    simp only [WTParams.Rdown, pow_zero, mul_one]
    exact Nat.floor_le (by positivity)
  | succ k ih =>
    simp only [WTParams.Rdown]
    push_cast
    calc ((P.Rdown k : ℝ) ^ (40 * P.d)) ^ (40 * P.d)
        ≤ ((Real.log P.L ^ (40 * P.d * (1600 * P.d ^ 2) ^ k)) ^ (40 * P.d)) ^ (40 * P.d) := by
          gcongr
      _ = Real.log P.L ^ (40 * P.d * (1600 * P.d ^ 2) ^ (k + 1)) := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          ring

/-- **Every order `n ≤ N_{p+1}^4` is at most `(log L)^{A(d,𝔇)}`** (for `d ≥ 1`, `log L ≥ 1`). -/
theorem le_logPow_ordExp (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ Real.log P.L) (p n : ℕ) (hn : n ≤ P.N (p + 1) ^ 4) :
    (n : ℝ) ≤ Real.log P.L ^ ((ordExp P.d P.D : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  have hL0 : 0 ≤ Real.log P.L := zero_le_one.trans hL
  have h1 : (n : ℝ) ≤ ((P.Rdown (P.D - (p + 1)) : ℝ) ^ (40 * P.d)) ^ 4 := by
    have : (n : ℝ) ≤ ((P.N (p + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hn
    simpa [WTParams.N, WTParams.R] using this
  refine h1.trans ?_
  calc ((P.Rdown (P.D - (p + 1)) : ℝ) ^ (40 * P.d)) ^ 4
      ≤ ((Real.log P.L ^ (40 * P.d * (1600 * P.d ^ 2) ^ (P.D - (p + 1)))) ^ (40 * P.d)) ^ 4 := by
        gcongr
        exact Rdown_le P hL0 _
    _ = Real.log P.L ^ (160 * P.d * (40 * P.d * (1600 * P.d ^ 2) ^ (P.D - (p + 1)))) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
    _ ≤ Real.log P.L ^ ordExp P.d P.D := by
        refine pow_le_pow_right₀ hL ?_
        unfold ordExp
        gcongr
        exact Nat.sub_le _ _

end WaveTurbulence.Regref
