/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftEnvelopeExponential
public import WaveTurbulence.Foundations.XChain.InductProbability
/-! The previous-stage input error beats every finite graft-count factor. -/
public section
namespace WaveTurbulence.Induct

theorem large_power_ge_quartic_count {N e : ℕ} (hN : 2000000 ≤ N) (he : 6 ≤ e) :
    1000000 * N ^ 4 + 20 * N ≤ N ^ e := by
  have hN1 : 1 ≤ N := by omega
  have h2 : 2000000 ≤ N ^ 2 := hN.trans (le_self_pow₀ hN1 (by decide))
  have h4 : N ≤ N ^ 4 := le_self_pow₀ hN1 (by decide)
  have h6 : 1000000 * N ^ 4 + 20 * N ≤ N ^ 6 := by
    have h := Nat.mul_le_mul_right (N ^ 4) h2
    rw [show 6 = 2 + 4 from rfl, pow_add]
    nlinarith
  exact h6.trans (Nat.pow_le_pow_right (by omega) he)

theorem previous_N_ge_quartic_count (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D)
    (hN : 2000000 ≤ P.N (p + 1)) :
    1000000 * (P.N (p + 1) : ℝ) ^ 4 + 20 * P.N (p + 1) ≤ (P.N p : ℝ) := by
  have hk : 6 ≤ (40 * P.d) * (40 * P.d) := by nlinarith
  have h := large_power_ge_quartic_count hN hk
  rw [← N_succ_relation P hp] at h
  exact_mod_cast h

theorem envelope_times_input_error_le_exp (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D)
    (hN : 2000000 ≤ P.N (p + 1)) {E : ℝ}
    (hE : E ≤ Real.exp (1000000 * (P.N (p + 1) : ℝ) ^ 4)) :
    E * Real.exp (-(P.N p : ℝ)) ≤ Real.exp (-(20 * (P.N (p + 1) : ℝ))) := by
  have h := mul_le_mul_of_nonneg_right hE (Real.exp_pos (-(P.N p : ℝ))).le
  rw [← Real.exp_add] at h
  exact h.trans (Real.exp_le_exp.mpr (by
    have hp' := previous_N_ge_quartic_count P hd hp hN
    linarith))

end WaveTurbulence.Induct
