/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Audit of the proposed circle-exponent substitution

The expression below is the two-branch annulus estimate in DH23, Appendix A,
Lemma `basiccount0pre` (1), after the rescaling used in `basiccount0` (2),
with circle discrepancy exponent `2/3`. This file proves facts about that
numerical expression, not about lattice counts or the circle problem.
-/

public section

namespace WaveTurbulence.Counting

/-- At `γ = 4/5` and `Q = L^(6/5)`, the proposed replacement has size
`L^(4/5)`. Source: DH23 TeX L2082; retain all three summands of the second
branch of `disclattice` (L2029). -/
theorem annulus_two_thirds_critical_value {L : ℝ} (hL : 0 < L) :
    min (L ^ ((2 : ℝ) / 5) + (L ^ ((6 : ℝ) / 5)) ^ ((2 : ℝ) / 3))
      (L ^ ((1 : ℝ) / 5) + L ^ ((8 : ℝ) / 5) * (L ^ ((6 : ℝ) / 5))⁻¹ +
        L ^ ((6 : ℝ) / 5) * (L ^ ((6 : ℝ) / 5)) ^ (-(1 : ℝ) / 3)) =
      L ^ ((2 : ℝ) / 5) + L ^ ((4 : ℝ) / 5) := by
  have hcircle : (L ^ ((6 : ℝ) / 5)) ^ ((2 : ℝ) / 3) =
      L ^ ((4 : ℝ) / 5) := by
    rw [← Real.rpow_mul hL.le]
    norm_num
  have hmiddle : L ^ ((8 : ℝ) / 5) * (L ^ ((6 : ℝ) / 5))⁻¹ =
      L ^ ((2 : ℝ) / 5) := by
    rw [← Real.rpow_neg hL.le, ← Real.rpow_add hL]
    norm_num
  have hlast : L ^ ((6 : ℝ) / 5) * (L ^ ((6 : ℝ) / 5)) ^ (-(1 : ℝ) / 3) =
      L ^ ((4 : ℝ) / 5) := by
    rw [← Real.rpow_mul hL.le, ← Real.rpow_add hL]
    norm_num
  rw [hcircle, hmiddle, hlast, min_eq_left]
  have hp := Real.rpow_pos_of_pos hL ((1 : ℝ) / 5)
  linarith only [hp]

/-- No uniform implicit constant repairs the lost strict power saving in
DH23 `basiccount0` (2) using this numerical expression alone. This is an
obstruction to the proposed deduction, not a lower bound for lattice counts. -/
theorem annulus_two_thirds_not_uniform_subpower (ε C : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧
      C * L ^ ((4 : ℝ) / 5 - ε) <
        min (L ^ ((2 : ℝ) / 5) + (L ^ ((6 : ℝ) / 5)) ^ ((2 : ℝ) / 3))
          (L ^ ((1 : ℝ) / 5) + L ^ ((8 : ℝ) / 5) * (L ^ ((6 : ℝ) / 5))⁻¹ +
            L ^ ((6 : ℝ) / 5) * (L ^ ((6 : ℝ) / 5)) ^ (-(1 : ℝ) / 3)) := by
  have hgrowth := (tendsto_rpow_atTop hε).eventually
    (Filter.eventually_gt_atTop C)
  obtain ⟨L, hpower, hL⟩ := (hgrowth.and (Filter.eventually_ge_atTop (1 : ℝ))).exists
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨L, hL, ?_⟩
  rw [annulus_two_thirds_critical_value hLpos]
  have hp := mul_lt_mul_of_pos_right hpower
    (Real.rpow_pos_of_pos hLpos ((4 : ℝ) / 5 - ε))
  have heq : L ^ ε * L ^ ((4 : ℝ) / 5 - ε) = L ^ ((4 : ℝ) / 5) := by
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  rw [heq] at hp
  exact hp.trans_le (le_add_of_nonneg_left (Real.rpow_nonneg hLpos.le _))

/-- The gain in the correctly summed `2/3` bound in the uses for
`basiccount0` (1) and (3) is `(2γ - 1)/3`. -/
theorem annulus_two_thirds_gain (γ : ℝ) :
    1 - (4 - 2 * γ) / 3 = (2 * γ - 1) / 3 := by ring

/-- Maximizing powers in each sum gives the following uniform exponent
bound for `basiccount0` (1), DH23 L2077, with discrepancy exponent `2/3`.
Here `q` is the exponent in `Q = L^q`. -/
theorem annulus_two_thirds_exponent_le {γ q : ℝ} (hγ : (1 : ℝ) / 2 ≤ γ) :
    min (max (2 - 2 * γ) (2 * q / 3))
      (max (1 - γ) (max (4 - 3 * γ - q) (2 - γ - q / 3))) ≤
        (4 - 2 * γ) / 3 := by
  by_cases hq : q ≤ 2 - γ
  · apply (min_le_left _ _).trans
    apply max_le <;> linarith only [hγ, hq]
  · apply (min_le_right _ _).trans
    apply max_le
    · linarith only [hγ]
    · apply max_le <;> linarith only [hγ, hq]

/-- The preceding exponent is attained at `q = 2 - γ`; a better uniform
power does not follow merely by optimizing these two branches. -/
theorem annulus_two_thirds_exponent_critical {γ : ℝ} (hγ : (1 : ℝ) / 2 ≤ γ) :
    min (max (2 - 2 * γ) (2 * (2 - γ) / 3))
      (max (1 - γ) (max (4 - 3 * γ - (2 - γ)) (2 - γ - (2 - γ) / 3))) =
        (4 - 2 * γ) / 3 := by
  apply le_antisymm (annulus_two_thirds_exponent_le hγ)
  apply le_min
  · apply (le_max_right _ _).trans'
    linarith only
  · apply ((le_max_right _ _).trans (le_max_right _ _)).trans'
    linarith only

/-- Keeping the sum in DH23 L2082, the original exponent `7/11` still
provides `63/80 < 4/5 - 1/10000`. The split is `q = 99/80`. -/
theorem annulus_seven_elevenths_exponent_le (q : ℝ) :
    min (max ((2 : ℝ) / 5) (7 * q / 11))
      (max ((1 : ℝ) / 5) (max (8 / 5 - q) (6 / 5 - q / 3))) ≤ (63 : ℝ) / 80 := by
  by_cases hq : q ≤ (99 : ℝ) / 80
  · apply (min_le_left _ _).trans
    apply max_le <;> linarith only [hq]
  · apply (min_le_right _ _).trans
    apply max_le
    · norm_num
    · apply max_le <;> linarith only [hq]

/-- The large-radius use in `basiccount` (5), DH23 L2117, retains the
required exponent. At `Q ≥ L^(2 - γ₀/10)`, these are the three powers in
the geometric branch; `γ₀ = min γ (1 - γ)`. -/
theorem annulus_large_radius_exponent_le {γ : ℝ} (hγ : 0 ≤ γ) :
    max (1 - γ)
      (max (2 - 3 * γ + min γ (1 - γ) / 10)
        (4 / 3 - γ + min γ (1 - γ) / 30)) ≤
      max 1 (2 - 2 * γ) - min γ (1 - γ) / 10 := by
  by_cases hhalf : γ ≤ (1 : ℝ) / 2
  · rw [min_eq_left (by linarith only [hhalf]),
      max_eq_right (by linarith only [hhalf] : (1 : ℝ) ≤ 2 - 2 * γ)]
    apply max_le
    · linarith only [hhalf]
    · apply max_le <;> linarith only [hγ, hhalf]
  · rw [min_eq_right (by linarith only [hhalf]),
      max_eq_left (by linarith only [hhalf] : 2 - 2 * γ ≤ (1 : ℝ))]
    apply max_le
    · linarith only [hhalf]
    · apply max_le <;> linarith only [hhalf]

/-- Ignoring the additional `O(η)` losses, the same optimized bound could
supply the target of `basiccount0` (2) only above `4/5 + 12η`, whereas the
source allows `γ > 4/5 - 10η`. -/
theorem annulus_two_thirds_target_exponent (γ η : ℝ) :
    (4 - 2 * γ) / 3 ≤ γ - 20 * η ↔ (4 : ℝ) / 5 + 12 * η ≤ γ := by
  constructor <;> intro h <;> linarith only [h]

end WaveTurbulence.Counting
