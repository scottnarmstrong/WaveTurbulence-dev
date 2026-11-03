/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Dirichlet approximation for quadratic Weyl sums

The rational approximation used in DH23, proof of Lemma 6.6 (near `refinedHua`),
and DH21, the paragraph preceding `GaussLem`. The numerator is an integer and the
positive denominator is a natural number; coprimality is expressed using `natAbs`.
-/

public section

namespace WaveTurbulence.WeylSums

/-- Dirichlet approximation with a positive denominator at most `K`.
This is the form used in packet NT.dirichlet; Mathlib supplies the slightly
stronger error `1 / ((K + 1) * q)`. -/
theorem exists_coprime_approx (t : ℝ) {K : ℕ} (hK : 1 ≤ K) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ K ∧ a.natAbs.Coprime q ∧
      |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * K) := by
  obtain ⟨r, hr, hrK⟩ := Real.exists_rat_abs_sub_le_and_den_le t (Nat.zero_lt_of_lt hK)
  refine ⟨r.num, r.den, r.pos, hrK, r.reduced, ?_⟩
  rw [← Rat.cast_def]
  refine hr.trans ?_
  apply one_div_le_one_div_of_le
  · exact mul_pos (Nat.cast_pos.mpr r.pos) (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hK))
  · have h : (K : ℝ) ≤ K + 1 := le_add_of_nonneg_right zero_le_one
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right h (Nat.cast_nonneg r.den)

end WaveTurbulence.WeylSums
