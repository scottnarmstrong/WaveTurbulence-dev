/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.InductWidthRange
/-! The prescribed logarithmic size recursion dominates log L at every stage. -/
public section
namespace WaveTurbulence.Induct

theorem log_le_Rdown (P : WTParams) (hd : 1 ≤ P.d) (hL : Real.exp 2 ≤ P.L) :
    ∀ k : ℕ, Real.log P.L ≤ (P.Rdown k : ℝ) := by
  have hL0 : 0 < P.L := (Real.exp_pos 2).trans_le hL
  have hx : 2 ≤ Real.log P.L := (Real.le_log_iff_exp_le hL0).mpr hL
  have hk : 2 ≤ 40 * P.d := by omega
  have hk0 : 40 * P.d ≠ 0 := by omega
  have hbase : Real.log P.L ≤ (P.Rdown 0 : ℝ) := by
    have hpow : Real.log P.L ^ 2 ≤ Real.log P.L ^ (40 * P.d) :=
      pow_le_pow_right₀ (by linarith) hk
    have hfloor := Nat.lt_floor_add_one (Real.log P.L ^ (40 * P.d))
    change Real.log P.L ≤ (⌊Real.log P.L ^ (40 * P.d)⌋₊ : ℝ)
    nlinarith
  intro k
  induction k with
  | zero => exact hbase
  | succ k ih =>
    have hr : 1 ≤ P.Rdown k := by
      have h := hx.trans ih
      exact_mod_cast (by linarith : (1 : ℝ) ≤ P.Rdown k)
    have h1 := le_self_pow₀ hr hk0
    have hp : 1 ≤ P.Rdown k ^ (40 * P.d) := one_le_pow₀ hr
    have h2 := le_self_pow₀ hp hk0
    exact ih.trans (by exact_mod_cast (h1.trans h2))

theorem log_le_N (P : WTParams) (hd : 1 ≤ P.d) (hL : Real.exp 2 ≤ P.L) (p : ℕ) :
    Real.log P.L ≤ (P.N p : ℝ) := by
  exact (log_le_Rdown P hd hL (P.D - p)).trans (by exact_mod_cast R_le_N P hd p)

end WaveTurbulence.Induct
