/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.TreeChoices

/-!
# Conversion between Fourier and paper frequencies

The Fourier phase is `2π i ξ t`, while the paper writes `π i α t`.
Doubling every resonance costs at most two per branching vertex.
-/

public section

open scoped ENNReal

namespace WaveTurbulence.Analysis

/-- The reciprocal bracket at half frequency loses at most a factor two. -/
theorem oscillatoryWeight_le_two_mul_double (x : ℝ) :
    oscillatoryWeight x ≤ 2 * oscillatoryWeight (2 * x) := by
  have hA : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 < Real.sqrt (1 + (2 * x) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hA2 := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hB2 := Real.sq_sqrt (show 0 ≤ 1 + (2 * x) ^ 2 by positivity)
  have hs : Real.sqrt (1 + (2 * x) ^ 2) ≤ 2 * Real.sqrt (1 + x ^ 2) := by
    nlinarith only [hA.le, hB.le, hA2, hB2]
  change (Real.sqrt (1 + x ^ 2))⁻¹ ≤ 2 * (Real.sqrt (1 + (2 * x) ^ 2))⁻¹
  rw [← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ hA hB).mpr (by simpa only [one_mul] using hs)

namespace IntegrationTree

/-- The complete product loses only `2^n` on converting to the source's
frequency normalization. -/
theorem choiceWeight_one_le_two (T : IntegrationTree) (d : T.Choice) :
    T.choiceWeight 1 d ≤ (2 : ℝ≥0∞) ^ T.branchCount * T.choiceWeight 2 d := by
  induction T with
  | leaf => simp only [choiceWeight, branchCount, pow_zero, one_mul, le_refl]
  | node a α σ₁ σ₂ σ₃ l m r hl hm hr =>
      have hJ := ENNReal.ofReal_le_ofReal
        (oscillatoryWeight_le_two_mul_double ((node a α σ₁ σ₂ σ₃ l m r).choiceResonance d))
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat] at hJ
      have hh := mul_le_mul' hJ (mul_le_mul' (mul_le_mul' (hl d.2.1.1) (hm d.2.1.2)) (hr d.2.2))
      change ENNReal.ofReal (oscillatoryWeight (1 * _)) * _ ≤ _
      rw [one_mul]
      refine hh.trans_eq ?_
      simp only [branchCount, choiceWeight, pow_add, pow_succ]
      ring

end IntegrationTree
end WaveTurbulence.Analysis
