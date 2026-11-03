/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.FrequencyIntegration

/-!
# Integer linear phases on the sampled lattice

Integer frequency normalization preserves the actual source samples.
Conjugation also provides the decreasing-derivative convention.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

theorem expPhase_sub_int_mul_nat_add_one (f : ℝ → ℝ) (m : ℤ) (n : ℕ) :
    expPhase (f ((n : ℝ) + 1) - (m : ℝ) * ((n : ℝ) + 1)) = expPhase (f ((n : ℝ) + 1)) := by
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
    expPhase_sub_int_mul_int f m ((n : ℤ) + 1)

/-- Exact invariance of the actual half-open sampled sum. -/
theorem sum_expPhase_sub_int_linear (f : ℝ → ℝ) (m : ℤ) (a b : ℕ) :
    (∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1) - (m : ℝ) * ((n : ℝ) + 1))) =
      ∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1)) := by
  apply Finset.sum_congr rfl
  intro n _
  exact expPhase_sub_int_mul_nat_add_one f m n

/-- Conjugating an integer linear phase minus the source phase recovers
the original actual sampled sum. -/
theorem conj_sum_expPhase_int_linear_sub (f : ℝ → ℝ) (m : ℤ) (a b : ℕ) :
    (starRingEnd ℂ) (∑ n ∈ Finset.Ico a b,
      expPhase ((m : ℝ) * ((n : ℝ) + 1) - f ((n : ℝ) + 1))) =
        ∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [conj_expPhase, show -((m : ℝ) * ((n : ℝ) + 1) - f ((n : ℝ) + 1)) =
    f ((n : ℝ) + 1) - (m : ℝ) * ((n : ℝ) + 1) by ring]
  exact expPhase_sub_int_mul_nat_add_one f m n

end WaveTurbulence.VdCB
