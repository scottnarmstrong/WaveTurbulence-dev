/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.WeightedL2Norm

/-!+# Weight transfer on the resonant set

The weight-transfer lemma in §5 of `docs/research/git20-general-d.md`.
The weight is exactly the multiplier in the frozen `weightedL2Norm`.
-/

public section

open scoped InnerProductSpace

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Energy conservation in the hyperplane parametrization of (C.5). -/
theorem energy_identity (k a b : Mom d) (hab : ⟪a, b⟫_ℝ = 0) :
    ‖k + a‖ ^ 2 + ‖k + b‖ ^ 2 = ‖k‖ ^ 2 + ‖k + a + b‖ ^ 2 := by
  rw [norm_add_sq_real (k + a) b, norm_add_sq_real k a,
    norm_add_sq_real k b, inner_add_left, hab]
  ring

/-- The output Japanese bracket squared is bounded by the sum of the input
brackets squared on the resonant set. -/
theorem bracket_sq_le (k a b : Mom d) (hab : ⟪a, b⟫_ℝ = 0) :
    1 + ‖k‖ ^ 2 ≤ (1 + ‖k + a‖ ^ 2) + (1 + ‖k + b‖ ^ 2) := by
  have he := energy_identity k a b hab
  linarith only [he, sq_nonneg ‖k + a + b‖]

/-- Weight transfer with the constant `2^(s/2)` of the research note, §5. -/
theorem weight_transfer (s : ℝ) (hs : 0 ≤ s) (k a b : Mom d)
    (hab : ⟪a, b⟫_ℝ = 0) :
    (1 + ‖k‖ ^ 2) ^ (s / 2) ≤
      (2 : ℝ) ^ (s / 2) *
        ((1 + ‖k + a‖ ^ 2) ^ (s / 2) + (1 + ‖k + b‖ ^ 2) ^ (s / 2)) := by
  have hp : 0 ≤ s / 2 := div_nonneg hs (by norm_num)
  have hx : 0 ≤ 1 + ‖k + a‖ ^ 2 := by positivity
  have hy : 0 ≤ 1 + ‖k + b‖ ^ 2 := by positivity
  have hm : (1 + ‖k + a‖ ^ 2) + (1 + ‖k + b‖ ^ 2) ≤
      2 * max (1 + ‖k + a‖ ^ 2) (1 + ‖k + b‖ ^ 2) := by
    linarith only [le_max_left (1 + ‖k + a‖ ^ 2) (1 + ‖k + b‖ ^ 2),
      le_max_right (1 + ‖k + a‖ ^ 2) (1 + ‖k + b‖ ^ 2)]
  calc
    (1 + ‖k‖ ^ 2) ^ (s / 2) ≤
        (2 * max (1 + ‖k + a‖ ^ 2) (1 + ‖k + b‖ ^ 2)) ^ (s / 2) :=
      Real.rpow_le_rpow (by positivity) ((bracket_sq_le k a b hab).trans hm) hp
    _ = (2 : ℝ) ^ (s / 2) *
        max ((1 + ‖k + a‖ ^ 2) ^ (s / 2)) ((1 + ‖k + b‖ ^ 2) ^ (s / 2)) := by
      rw [Real.mul_rpow (by norm_num) (le_max_of_le_left hx), Real.rpow_max hx hy hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (max_le (le_add_of_nonneg_right (Real.rpow_nonneg hy _))
        (le_add_of_nonneg_left (Real.rpow_nonneg hx _))) (by positivity)

end WaveTurbulence.WKEL2
