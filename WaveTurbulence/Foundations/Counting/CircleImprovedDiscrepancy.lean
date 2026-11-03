/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleEndpointBound
public import WaveTurbulence.Foundations.Counting.CircleLocalizedEndpointTransfer
import Mathlib.Tactic

/-!
# Uniform circle discrepancy with exponent 27/41

The actual endpoint-block estimate discharges every analytic hypothesis
of the localized circle transfer. This proves the improved discrepancy
uniformly in the real center, using only the proved A/B analysis.
-/

public section

namespace WaveTurbulence.Counting

/-- A concrete absolute constant for the proved improved circle bound. -/
@[expose] noncomputable def circleImprovedConstant : ℝ :=
  2668+8*((Real.pi/((11:ℝ)/30)+1/(1-((11:ℝ)/30)))/Real.pi^2)*
    (6+400000000000/((2:ℝ)^((7:ℝ)/20)-1))

theorem circleImprovedConstant_pos : 0 < circleImprovedConstant := by
  have hden : 0 < (2:ℝ)^((7:ℝ)/20)-1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  unfold circleImprovedConstant
  positivity

/-- Actual dyadic endpoint blocks have the local transformed circle powers. -/
theorem norm_sum_circle_dyadic_endpoint_block_le {R c : ℝ} (n m : ℕ) (hn : 0 < n)
    (hU : 1 ≤ R/(2:ℝ)^(m+1)) (hUR : 3*(R/(2:ℝ)^(m+1)) ≤ R) :
    ‖∑ x ∈ (integerInterval (c-R) (c+R)).filter (fun x : ℤ =>
      R/Real.sqrt 2 < |(x:ℝ)-c| ∧ R/(2:ℝ)^(m+1) < R-|(x:ℝ)-c| ∧
        R-|(x:ℝ)-c| ≤ R/(2:ℝ)^m), NumberTheory.expPhase ((n:ℝ)*circleHeight R c x)‖ ≤
      400000000000*((n:ℝ)^((11:ℝ)/30)*R^((11:ℝ)/60)*(R/(2:ℝ)^(m+1))^((7:ℝ)/20)) := by
  have hd : R/(2:ℝ)^m = 2*(R/(2:ℝ)^(m+1)) := by
    rw [pow_succ]
    field_simp
  rw [hd]
  exact norm_sum_circle_endpoint_block_le hU hUR (by exact_mod_cast hn)

/-- The circle problem with exponent strictly below two thirds, uniformly
in every real center, for the actual closed lattice disc. -/
theorem abs_card_latticeDisc_sub_area_le_twenty_seven_forty_one
    {Q : ℝ} (hQ : 1 ≤ Q) (c : EuclideanSpace ℝ (Fin 2)) :
    |((latticeDisc c Q).card:ℝ)-Real.pi*Q^2| ≤ circleImprovedConstant*Q^((27:ℝ)/41) := by
  have he := abs_card_latticeDisc_sub_area_le_of_localized_endpoint_power_bounds c hQ
    (C := 400000000000) (kappa := (11:ℝ)/30) (lambda := (16:ℝ)/30)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j n hn m hU hUR => by
      have hb := norm_sum_circle_dyadic_endpoint_block_le (c := c j) n m hn hU hUR
      norm_num only [show ((11:ℝ)/30)/2 = 11/60 by norm_num,
        show ((16:ℝ)/30)-((11:ℝ)/30)/2 = 7/20 by norm_num]
      simpa only [mul_assoc] using! hb)
  simpa only [circleImprovedConstant,
    show ((16:ℝ)/30)-((11:ℝ)/30)/2 = 7/20 by norm_num,
    show (((11:ℝ)/30)+(16:ℝ)/30)/(1+(11:ℝ)/30) = 27/41 by norm_num] using! he

/-- The proved circle exponent is strictly stronger than two thirds. -/
theorem circle_improved_exponent_lt_two_thirds : (27:ℝ)/41 < 2/3 := by norm_num

end WaveTurbulence.Counting
