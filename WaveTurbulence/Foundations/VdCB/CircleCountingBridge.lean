/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleEndpointBlock
public import WaveTurbulence.Foundations.Counting.CircleEndpointTransfer

/-!
# The direct circle-family B-process consumed by counting

These theorems discharge the actual endpoint exponential-sum input of
the landed counting transfer. The improved exponent is `27/41 < 2/3`.
The proof uses the actual circle family, not a generic profile closure axiom.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Uniform constant for both reflected endpoint octants. -/
@[expose] noncomputable def circleEndpointConstant : ℝ := 2 * (circleBConstant + 1)

theorem circleEndpointConstant_pos : 0 < circleEndpointConstant := by
  unfold circleEndpointConstant circleBConstant
  positivity

/-- Exact endpoint-block interface, valid for every real block scale at least one. -/
theorem norm_sum_circle_endpoint_block_le {R c U : ℝ} (hR : 1 ≤ R) (hU : 1 ≤ U)
    (n : ℕ) (hn : 0 < n) :
    ‖∑ x ∈ (Counting.integerInterval (c - R) (c + R)).filter (fun x : ℤ =>
        R / Real.sqrt 2 < |(x : ℝ) - c| ∧ U < R - |(x : ℝ) - c| ∧
          R - |(x : ℝ) - c| ≤ 2 * U),
      expPhase ((n : ℝ) * Counting.circleHeight R c x)‖ ≤
    circleEndpointConstant * (n : ℝ) ^ (11 / 30 : ℝ) * R ^ (11 / 60 : ℝ) * U ^ (7 / 20 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := norm_sum_circleEndpointBlock_le (c := c) (zero_lt_one.trans_le hR) hU hn1
  convert hs using 1
  · rfl
  · unfold circleEndpointConstant circleBScale
    ring

/-- The exact dyadic block statement requested by `CircleEndpointTransfer`. -/
theorem norm_sum_circle_endpoint_dyadic_le {R : ℝ} (hR : 1 ≤ R) (c : ℝ)
    (n : ℕ) (hn : 0 < n) (m : ℕ) (hU : 1 ≤ R / (2 : ℝ) ^ (m + 1)) :
    ‖∑ x ∈ (Counting.integerInterval (c - R) (c + R)).filter (fun x : ℤ =>
        R / Real.sqrt 2 < |(x : ℝ) - c| ∧ R / (2 : ℝ) ^ (m + 1) < R - |(x : ℝ) - c| ∧
          R - |(x : ℝ) - c| ≤ R / (2 : ℝ) ^ m),
      expPhase ((n : ℝ) * Counting.circleHeight R c x)‖ ≤
    circleEndpointConstant * (n : ℝ) ^ (11 / 30 : ℝ) * R ^ ((11 / 30 : ℝ) / 2) *
      (R / (2 : ℝ) ^ (m + 1)) ^ ((16 / 30 : ℝ) - (11 / 30 : ℝ) / 2) := by
  have he : 2 * (R / (2 : ℝ) ^ (m + 1)) = R / (2 : ℝ) ^ m := by
    rw [pow_succ]
    field_simp
  simpa only [he, show ((11 / 30 : ℝ) / 2) = 11 / 60 by norm_num,
    show ((16 / 30 : ℝ) - 11 / 60) = 7 / 20 by norm_num] using
    norm_sum_circle_endpoint_block_le (c := c) hR hU n hn

/-- The counting constant resulting from the actual source B-process. -/
@[expose] noncomputable def circleDiscrepancyConstant : ℝ :=
  2668 + 8 * ((Real.pi / (11 / 30 : ℝ) + 1 / (1 - (11 / 30 : ℝ))) / Real.pi ^ 2) *
    (6 + circleEndpointConstant / ((2 : ℝ) ^ ((16 / 30 : ℝ) - (11 / 30 : ℝ) / 2) - 1))

/-- Unconditional uniform translated closed-disc discrepancy below exponent `2/3`. -/
theorem abs_card_latticeDisc_sub_area_le (c : EuclideanSpace ℝ (Fin 2))
    {R : ℝ} (hR : 1 ≤ R) :
    |((Counting.latticeDisc c R).card : ℝ) - Real.pi * R ^ 2| ≤
      circleDiscrepancyConstant * R ^ (27 / 41 : ℝ) := by
  have hs := Counting.abs_card_latticeDisc_sub_area_le_of_endpoint_power_bounds c hR
    circleEndpointConstant_pos.le (by norm_num : (0 : ℝ) < 11 / 30)
    (by norm_num : (11 / 30 : ℝ) < 1) (by norm_num : (1 / 2 : ℝ) ≤ 16 / 30)
    (by norm_num : (16 / 30 : ℝ) ≤ 1)
    (fun j n hn m hU => norm_sum_circle_endpoint_dyadic_le hR (c j) n hn m hU)
  simpa only [circleDiscrepancyConstant,
    show ((11 / 30 : ℝ) + 16 / 30) / (1 + 11 / 30) = 27 / 41 by norm_num] using hs

/-- The same unconditional source estimate supplies the counting annulus input. -/
theorem card_annulus_le (s : Finset (Fin 2 → ℤ)) (c : EuclideanSpace ℝ (Fin 2))
    {Q rho : ℝ} (hQ : 2 ≤ Q) (hrho : 0 < rho) (hrhoQ : rho ≤ Q / 4)
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n - c‖ - Q| ≤ rho) :
    (s.card : ℝ) ≤ (6 * Real.pi) * (Q * rho) +
      (3 * circleDiscrepancyConstant) * Q ^ (27 / 41 : ℝ) := by
  have hs := Counting.card_annulus_le_of_endpoint_power_bounds s c hQ hrho hrhoQ
    circleEndpointConstant_pos.le (by norm_num : (0 : ℝ) < 11 / 30)
    (by norm_num : (11 / 30 : ℝ) < 1) (by norm_num : (1 / 2 : ℝ) ≤ 16 / 30)
    (by norm_num : (16 / 30 : ℝ) ≤ 1)
    (fun R hR j n hn m hU => norm_sum_circle_endpoint_dyadic_le hR (c j) n hn m hU) hann
  simpa only [circleDiscrepancyConstant,
    show ((11 / 30 : ℝ) + 16 / 30) / (1 + 11 / 30) = 27 / 41 by norm_num] using hs

end WaveTurbulence.VdCB
