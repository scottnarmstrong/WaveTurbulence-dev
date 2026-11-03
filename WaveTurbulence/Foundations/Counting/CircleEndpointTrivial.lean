/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleEndpointIntervals
public import WaveTurbulence.Foundations.NumberTheory.StationaryErrorBounds
import Mathlib.Tactic

/-!
# The large-frequency range of the actual endpoint block

Each endpoint window contains at most `U+1` integer columns. If the
frequency scale `h sqrt(R)` exceeds `U²`, the actual trivial sum bound
already has the improved local circle powers.
-/

public section

namespace WaveTurbulence.Counting

/-- Both exact endpoint windows have at most their length plus one points. -/
theorem card_circleEndpoint_windows_le {R c U : ℝ} (hU : 0 ≤ U) :
    ((circleEndpointLeft R c U).card:ℝ) ≤ U+1 ∧
      ((circleEndpointRight R c U).card:ℝ) ≤ U+1 := by
  have hl : circleEndpointLeft R c U ⊆
      integerInterval ((c-R+3*U/2)-U/2) ((c-R+3*U/2)+U/2) := by
    intro n hn
    obtain ⟨h1,h2,_h3⟩ := (mem_circleEndpointLeft R c U n).mp hn
    apply (mem_integerInterval _ _ _).mpr
    constructor <;> linarith only [h1,h2]
  have hr : circleEndpointRight R c U ⊆
      integerInterval ((c+R-3*U/2)-U/2) ((c+R-3*U/2)+U/2) := by
    intro n hn
    obtain ⟨h1,_h2,h3⟩ := (mem_circleEndpointRight R c U n).mp hn
    apply (mem_integerInterval _ _ _).mpr
    constructor <;> linarith only [h1,h3]
  have hcl : ((circleEndpointLeft R c U).card:ℝ) ≤
      (integerInterval ((c-R+3*U/2)-U/2) ((c-R+3*U/2)+U/2)).card := by
    exact_mod_cast Finset.card_le_card hl
  have hcr : ((circleEndpointRight R c U).card:ℝ) ≤
      (integerInterval ((c+R-3*U/2)-U/2) ((c+R-3*U/2)+U/2)).card := by
    exact_mod_cast Finset.card_le_card hr
  have hbl := card_integerInterval_le (c-R+3*U/2) (show 0 ≤ U/2 by positivity)
  have hbr := card_integerInterval_le (c+R-3*U/2) (show 0 ≤ U/2 by positivity)
  constructor <;> linarith only [hcl,hcr,hbl,hbr]

/-- Uniform actual sum bound from the two short integer windows. -/
theorem norm_circle_endpoint_block_sum_le_length (f : ℤ → ℝ)
    {R c U : ℝ} (hR : 0 < R) (hU : 1 ≤ U) :
    ‖∑ n ∈ (integerInterval (c-R) (c+R)).filter (fun n : ℤ =>
      R/Real.sqrt 2 < |(n:ℝ)-c| ∧ U < R-|(n:ℝ)-c| ∧ R-|(n:ℝ)-c| ≤ 2*U),
      NumberTheory.expPhase (f n)‖ ≤ 4*U := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  rw [sum_circle_endpoint_block_eq _ hR hUp]
  have hcard := card_circleEndpoint_windows_le (R := R) (c := c) hUp.le
  have hnorm (s : Finset ℤ) : ‖∑ n ∈ s, NumberTheory.expPhase (f n)‖ ≤ (s.card:ℝ) := by
    calc
      _ ≤ ∑ n ∈ s, ‖NumberTheory.expPhase (f n)‖ := norm_sum_le _ _
      _ = _ := by simp only [NumberTheory.norm_expPhase,Finset.sum_const,nsmul_eq_mul,mul_one]
  have hh := (norm_add_le _ _).trans (add_le_add
    ((hnorm _).trans hcard.1) ((hnorm _).trans hcard.2))
  linarith only [hh,hU]

/-- The large-frequency range of the actual circle block satisfies the
local `(11/30,16/30)` estimate without any analytic B-process input. -/
theorem norm_circle_endpoint_block_sum_le_of_large_frequency
    {R c U h : ℝ} (hR : 0 < R) (hh : 0 < h) (hU : 1 ≤ U)
    (hlarge : U^2 ≤ h*Real.sqrt R) :
    ‖∑ n ∈ (integerInterval (c-R) (c+R)).filter (fun n : ℤ =>
      R/Real.sqrt 2 < |(n:ℝ)-c| ∧ U < R-|(n:ℝ)-c| ∧ R-|(n:ℝ)-c| ≤ 2*U),
      NumberTheory.expPhase (h*circleHeight R c n)‖ ≤
        4*(h^((11:ℝ)/30)*R^((11:ℝ)/60)*U^((7:ℝ)/20)) := by
  have hwp : 0 < h*Real.sqrt R := mul_pos hh (Real.sqrt_pos.mpr hR)
  have hscale := NumberTheory.local_circle_scale_dominates_length hU hwp hlarge
  have he : (h*Real.sqrt R)^((11:ℝ)/30) = h^((11:ℝ)/30)*R^((11:ℝ)/60) := by
    rw [Real.mul_rpow hh.le (Real.sqrt_nonneg R),Real.sqrt_eq_rpow,← Real.rpow_mul hR.le]
    norm_num
  rw [he] at hscale
  exact (norm_circle_endpoint_block_sum_le_length _ hR hU).trans
    (mul_le_mul_of_nonneg_left hscale (by norm_num))

end WaveTurbulence.Counting
