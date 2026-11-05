/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.InductProbability
/-! All leaf blocks needed by the next-stage moments lie in the previous actual cumulant range. -/
public section
namespace WaveTurbulence.Induct

theorem R_le_N (P : WTParams) (hd : 1 ≤ P.d) (p : ℕ) : P.R p ≤ P.N p := by
  have hk : 40 * P.d ≠ 0 := by omega
  by_cases hR : P.R p = 0
  · simp only [WTParams.N, hR, zero_pow hk, le_refl]
  · exact le_self_pow₀ (by omega : 1 ≤ P.R p) hk

theorem top_leaf_count_le_previous_range (P : WTParams) (hd : 1 ≤ P.d)
    {p : ℕ} (hp : p < P.D) (hN : 2 ≤ P.N (p + 1)) {w : ℕ}
    (hw : w ≤ 100 * P.R (p + 1)) :
    w * (2 * P.N (p + 1) + 1) ≤ 2 * P.R p := by
  let N := P.N (p + 1)
  have hk : 10 ≤ 40 * P.d := by omega
  have hwN : w ≤ 100 * N := hw.trans (Nat.mul_le_mul_left 100 (R_le_N P hd (p + 1)))
  have hsmall : w * (2 * N + 1) ≤ 300 * N ^ 2 := by
    have h := Nat.mul_le_mul_right (2 * N + 1) hwN
    nlinarith
  have hp8 : 256 ≤ N ^ 8 := by
    have h := Nat.pow_le_pow_left hN 8
    norm_num at h ⊢
    exact h
  have h10 : 300 * N ^ 2 ≤ 2 * N ^ 10 := by
    have h := Nat.mul_le_mul_right (N ^ 2) hp8
    rw [show 10 = 8 + 2 from rfl, pow_add]
    nlinarith
  have hK : N ^ 10 ≤ N ^ (40 * P.d) := Nat.pow_le_pow_right (by omega) hk
  rw [R_succ_relation P hp]
  exact hsmall.trans (h10.trans (Nat.mul_le_mul_left 2 hK))

end WaveTurbulence.Induct
