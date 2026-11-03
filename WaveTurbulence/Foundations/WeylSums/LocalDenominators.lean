/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.LocalArcIntegration

/-!
# The denominator gain on a short minor-arc window

DH23 Lemma 6.6(2), the summation after `refinedHua`. Nonzero numerators
force `q ≥ (2T)⁻¹`. Splitting off a convergent `q^(-1-ε)` series gives
`T^(σ-1-ε)`, with an arbitrarily small loss absorbed by the source's `η`.
-/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- A nonempty numerator range forces the large-denominator condition. -/
theorem one_le_two_mul_denominator {T : ℝ} {q : ℕ}
    (hne : (localNumerators T q).Nonempty) : 1 ≤ 2 * (q : ℝ) * T := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨ha0, hal, hau⟩ := mem_erase.mp ha |>.imp_right mem_Icc.mp
  have hM : 1 ≤ ⌊2 * (q : ℝ) * T⌋₊ := by omega
  simpa only [Nat.cast_one] using (Nat.le_floor_iff' (by omega : (1 : ℕ) ≠ 0)).mp hM

/-- A denominator power may be split at any exponent strictly above one. -/
theorem denominator_power_split {q : ℕ} (hq : 1 ≤ q) (σ ε : ℝ) :
    (q : ℝ) ^ (1-σ) = (q : ℝ) ^ (2-σ+ε) * (q : ℝ) ^ (-1-ε) := by
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  rw [← Real.rpow_add hqpos]
  congr 1
  ring

/-- Quantitative denominator summation on a local window, with any small loss. -/
theorem sum_localNumerators_rpow_le {T σ ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) (hσε : ε < σ-2) (N : ℕ) :
    (∑ q ∈ Icc 1 N, ((localNumerators T q).card : ℝ) * (q : ℝ)^(-σ)) ≤
      4*T*(1/(2*T))^(2-σ+ε) * ∑' q : ℕ, (q : ℝ)^(-1-ε) := by
  have hB : 0 < 1/(2*T) := by positivity
  have hb : 2-σ+ε < 0 := by linarith only [hσε]
  have hsum : (∑ q ∈ Icc 1 N, ((localNumerators T q).card : ℝ) * (q : ℝ)^(-σ)) ≤
      4*T*(1/(2*T))^(2-σ+ε) * ∑ q ∈ Icc 1 N, (q : ℝ)^(-1-ε) := by
    rw [mul_sum]
    apply sum_le_sum
    intro q hqmem
    have hq : 1 ≤ q := (mem_Icc.mp hqmem).1
    have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
    by_cases hne : (localNumerators T q).Nonempty
    · have hqB : 1/(2*T) ≤ (q : ℝ) := by
        apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
        nlinarith only [one_le_two_mul_denominator hne]
      have hpow : (q : ℝ)^(2-σ+ε) ≤ (1/(2*T))^(2-σ+ε) :=
        Real.rpow_le_rpow_of_nonpos hB hqB hb.le
      calc
        _ ≤ (4*(q : ℝ)*T) * (q : ℝ)^(-σ) :=
          mul_le_mul_of_nonneg_right (localNumerators_card_le hT.le q) (Real.rpow_nonneg hqpos.le _)
        _ = 4*T*(q : ℝ)^(1-σ) := by
          rw [sub_eq_add_neg, Real.rpow_add hqpos, Real.rpow_one]
          ring
        _ = 4*T*((q : ℝ)^(2-σ+ε)*(q : ℝ)^(-1-ε)) := by rw [denominator_power_split hq]
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hqpos.le (-1-ε))
          have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 4*T)
          simpa only [mul_assoc] using hh'
    · rw [not_nonempty_iff_eq_empty.mp hne]
      simp only [card_empty, Nat.cast_zero, zero_mul]
      positivity
  refine hsum.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Real.summable_nat_rpow.mpr (by linarith : -1-ε < -1)).sum_le_tsum (Icc 1 N)
    (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg q) _)

end WaveTurbulence.WeylSums
