/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.RationalArcCover
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Integrating the rational-arc envelope

Arc mass is `O(L⁻²)`. Counting candidate numerators leaves the denominator
sum `Σ q^(1-σ)`: harmonic at `σ=2`, and uniformly bounded for `σ>2`.
-/

public section

open MeasureTheory Finset
open scoped BigOperators

namespace WaveTurbulence.WeylSums

/-- The remaining denominator sum after integrating the rational arcs. -/
@[expose] noncomputable def arcDenominatorSum (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 N, (q : ℝ) ^ (1 - σ)

theorem integrable_rationalArcEnvelope {L σ : ℝ} (hL : 0 < L) (hσ : 1 < σ) (N : ℕ) :
    Integrable (rationalArcEnvelope L σ N) := by
  apply integrable_finsetSum
  intro q _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro a _
  exact integrable_scaledArcProfile hL hσ _

/-- Exact integral of the finite rational cover. -/
theorem integral_rationalArcEnvelope {L σ : ℝ} (hL : 0 < L) (hσ : 1 < σ) (N : ℕ) :
    (∫ t : ℝ, rationalArcEnvelope L σ N t) =
      arcProfileMass σ / L ^ 2 * ∑ q ∈ Icc 1 N, ((q : ℝ) + 3) * (q : ℝ) ^ (-σ) := by
  unfold rationalArcEnvelope
  have hint (q : ℕ) : Integrable (fun t : ℝ => (q : ℝ) ^ (-σ) *
      ∑ a ∈ Icc (-1 : ℤ) ((q : ℤ) + 1), scaledArcProfile L σ ((a : ℝ) / (q : ℝ)) t) :=
    (integrable_finsetSum (Icc (-1 : ℤ) ((q : ℤ) + 1))
      (fun a _ => integrable_scaledArcProfile hL hσ ((a : ℝ) / (q : ℝ)))).const_mul _
  rw [integral_finsetSum (Icc 1 N) (fun q _ => hint q)]
  rw [mul_sum]
  apply sum_congr rfl
  intro q _
  rw [integral_const_mul, integral_finsetSum (Icc (-1 : ℤ) ((q : ℤ) + 1))
    (fun a _ => integrable_scaledArcProfile hL hσ ((a : ℝ) / (q : ℝ)))]
  simp_rw [integral_scaledArcProfile hL]
  rw [sum_const, nsmul_eq_mul, numerator_range_card]
  push_cast
  ring

/-- At most four times the denominator power sum remains. -/
theorem integral_rationalArcEnvelope_le {L σ : ℝ} (hL : 0 < L) (hσ : 1 < σ) (N : ℕ) :
    (∫ t : ℝ, rationalArcEnvelope L σ N t) ≤
      4 * (arcProfileMass σ / L ^ 2) * arcDenominatorSum σ N := by
  rw [integral_rationalArcEnvelope hL hσ]
  have hsum : (∑ q ∈ Icc 1 N, ((q : ℝ) + 3) * (q : ℝ) ^ (-σ)) ≤
      4 * arcDenominatorSum σ N := by
    rw [arcDenominatorSum, mul_sum]
    apply sum_le_sum
    intro q hq
    have hq' : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (mem_Icc.mp hq).1
    have hqp : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq'
    calc
      _ ≤ (4 * (q : ℝ)) * (q : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hq']) (Real.rpow_nonneg hqp.le _)
      _ = 4 * (q : ℝ) ^ (1 - σ) := by
        rw [sub_eq_add_neg, Real.rpow_add hqp, Real.rpow_one]
        ring
  have hh := mul_le_mul_of_nonneg_left hsum
    (div_nonneg (arcProfileMass_nonneg σ) (sq_nonneg L))
  simpa only [mul_assoc, mul_left_comm] using hh

/-- The fourth-moment endpoint is the harmonic sum. -/
theorem arcDenominatorSum_two (N : ℕ) : arcDenominatorSum 2 N = (harmonic N : ℝ) := by
  unfold arcDenominatorSum
  norm_num only [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
  rw [harmonic_eq_sum_Icc]
  push_cast
  rfl

/-- Above the fourth-moment endpoint the denominator series converges. -/
theorem summable_arc_denominators {σ : ℝ} (hσ : 2 < σ) :
    Summable (fun q : ℕ => (q : ℝ) ^ (1 - σ)) :=
  Real.summable_nat_rpow.mpr (by linarith only [hσ])

theorem arcDenominatorSum_le_tsum {σ : ℝ} (hσ : 2 < σ) (N : ℕ) :
    arcDenominatorSum σ N ≤ ∑' q : ℕ, (q : ℝ) ^ (1 - σ) :=
  (summable_arc_denominators hσ).sum_le_tsum (Icc 1 N)
    (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg q) _)

end WaveTurbulence.WeylSums
