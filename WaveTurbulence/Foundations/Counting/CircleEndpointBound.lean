/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleEndpointIntervals
public import WaveTurbulence.Foundations.NumberTheory.CircleIntegerSourceWindow
import Mathlib.Tactic

/-!
# The unconditional improved endpoint-block exponential-sum bound

Apply the actual circle source theorem to both exact integer windows.
All centers, integer endpoints, strict octant boundaries and frequency
ranges are retained. This discharges the analytic input of the circle
and full annulus discrepancy transfer.
-/

public section

namespace WaveTurbulence.Counting

open NumberTheory

/-- Actual right endpoint window with the transformed circle powers. -/
theorem norm_sum_circleEndpointRight_le {R c U h : ℝ}
    (hU : 1 ≤ U) (hUR : 3*U ≤ R) (hh : 1 ≤ h) :
    ‖∑ n ∈ circleEndpointRight R c U, expPhase (h*circleHeight R c n)‖ ≤
      200000000000*VdCB.circleBScale R h U := by
  have hR : 0 < R := by linarith only [hU,hUR]
  let A : ℤ := max ⌈c+R-2*U⌉ (⌊c+R/Real.sqrt 2⌋+1)
  let B : ℤ := ⌈c+R-U⌉-1
  by_cases hAB : A ≤ B
  · have ha : A ∈ circleEndpointRight R c U := by change A ∈ Finset.Icc A B; simp only [Finset.mem_Icc]; exact ⟨le_rfl,hAB⟩
    have hb : B ∈ circleEndpointRight R c U := by change B ∈ Finset.Icc A B; simp only [Finset.mem_Icc]; exact ⟨hAB,le_rfl⟩
    have haR := (mem_circleEndpointRight R c U A).mp ha
    have hbR := (mem_circleEndpointRight R c U B).mp hb
    have he := norm_sum_circleColumnPhase_Icc_le_BScale A B hU hUR hh
      (by linarith only [haR.1]) (by linarith only [hbR.2.2]) haR.2.1.le
    simpa only [VdCB.circleColumnPhase,circleHeight,circleEndpointRight,A,B] using! he
  · have he : circleEndpointRight R c U = ∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hAB)
    rw [he,Finset.sum_empty,norm_zero]
    unfold VdCB.circleBScale
    positivity

/-- Actual left endpoint window with precisely the same constant. -/
theorem norm_sum_circleEndpointLeft_le {R c U h : ℝ}
    (hU : 1 ≤ U) (hUR : 3*U ≤ R) (hh : 1 ≤ h) :
    ‖∑ n ∈ circleEndpointLeft R c U, expPhase (h*circleHeight R c n)‖ ≤
      200000000000*VdCB.circleBScale R h U := by
  have hR : 0 < R := by linarith only [hU,hUR]
  let A : ℤ := ⌊c-R+U⌋+1
  let B : ℤ := min ⌊c-R+2*U⌋ (⌈c-R/Real.sqrt 2⌉-1)
  by_cases hAB : A ≤ B
  · have ha : A ∈ circleEndpointLeft R c U := by change A ∈ Finset.Icc A B; simp only [Finset.mem_Icc]; exact ⟨le_rfl,hAB⟩
    have hb : B ∈ circleEndpointLeft R c U := by change B ∈ Finset.Icc A B; simp only [Finset.mem_Icc]; exact ⟨hAB,le_rfl⟩
    have haR := (mem_circleEndpointLeft R c U A).mp ha
    have hbR := (mem_circleEndpointLeft R c U B).mp hb
    have he := norm_sum_circleColumnPhase_Icc_left_le_BScale A B hU hUR hh haR.1.le hbR.2.1 hbR.2.2.le
    simpa only [VdCB.circleColumnPhase,circleHeight,circleEndpointLeft,A,B] using! he
  · have he : circleEndpointLeft R c U = ∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hAB)
    rw [he,Finset.sum_empty,norm_zero]
    unfold VdCB.circleBScale
    positivity

/-- The actual two-sided clipped octant block satisfies the local powers
of `(11/30,16/30)`, with an absolute constant and no analytic hypotheses. -/
theorem norm_sum_circle_endpoint_block_le {R c U h : ℝ}
    (hU : 1 ≤ U) (hUR : 3*U ≤ R) (hh : 1 ≤ h) :
    ‖∑ n ∈ (integerInterval (c-R) (c+R)).filter (fun n : ℤ =>
      R/Real.sqrt 2 < |(n:ℝ)-c| ∧ U < R-|(n:ℝ)-c| ∧ R-|(n:ℝ)-c| ≤ 2*U),
      expPhase (h*circleHeight R c n)‖ ≤
      400000000000*(h^((11:ℝ)/30)*R^((11:ℝ)/60)*U^((7:ℝ)/20)) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hR : 0 < R := (by positivity : 0 < 3*U).trans_le hUR
  rw [sum_circle_endpoint_block_eq _ hR hUp]
  have he := (norm_add_le _ _).trans (add_le_add
    (norm_sum_circleEndpointLeft_le (c := c) hU hUR hh)
    (norm_sum_circleEndpointRight_le (c := c) hU hUR hh))
  unfold VdCB.circleBScale at he
  linarith only [he]

end WaveTurbulence.Counting
