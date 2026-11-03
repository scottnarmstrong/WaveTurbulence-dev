/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleOctantCounting
public import WaveTurbulence.Foundations.Counting.CircleOctantArea
import Mathlib.Tactic

/-!
# Circle discrepancy reduced to outer-octant sawtooth sums

The actual translated closed-disc discrepancy is bounded by four outer-cap
sawtooth sums and a square-root error. The artificial square edges cancel
exactly; their remaining correction has absolute value at most one.
-/

public section

namespace WaveTurbulence.Counting

/-- The actual sawtooth sum on the two outer caps in one coordinate
 direction, with an arbitrary vertical phase shift. -/
@[expose] noncomputable def circleCapSawtooth (R T c d : ℝ) : ℝ := by
  classical
  exact ∑ x ∈ (integerInterval (c-R) (c+R)).filter (fun x : ℤ => T < |(x:ℝ)-c|),
    NumberTheory.sawtooth (circleHeight R c x+d)

/-- Unconditional reduction to outer-octant sums, uniformly in both real
center coordinates, with all circular boundaries included. -/
theorem abs_card_latticeDisc_sub_area_le_outer_sawtooth
    (c : EuclideanSpace ℝ (Fin 2)) {R : ℝ} (hR : 2 ≤ R) :
    |((latticeDisc c R).card:ℝ)-Real.pi*R^2| ≤ 60*Real.sqrt R+17+
      |circleCapSawtooth R (R/Real.sqrt 2) (c 0) (c 1)|+
      |circleCapSawtooth R (R/Real.sqrt 2) (c 0) (-c 1)|+
      |circleCapSawtooth R (R/Real.sqrt 2) (c 1) (c 0)|+
      |circleCapSawtooth R (R/Real.sqrt 2) (c 1) (-c 0)| := by
  classical
  have hRp : 0 < R := by linarith only [hR]
  have hsqrt : 0 < Real.sqrt (2:ℝ) := by positivity
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hsqrt2 : Real.sqrt (2:ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  let T : ℝ := R/Real.sqrt 2
  have hT1 : 1 ≤ T := (le_div_iff₀ hsqrt).mpr (by linarith only [hR,hsqrt2])
  have hT0 : 0 ≤ T := le_trans zero_le_one hT1
  have hTR : 2*T^2 = R^2 := circle_octant_cut_sq R
  have hTRle : T ≤ R := div_le_self hRp.le hsqrt1
  let N : Fin 2 → ℝ := fun j => ((integerInterval (c j-T) (c j+T)).card:ℝ)
  let H : Fin 2 → ℝ := fun j => ∑ x ∈ integerInterval (c j-R) (c j+R), circleClippedHeight R T (c j) x
  let P : Fin 2 → ℝ → ℝ := fun j d => circleCapSawtooth R T (c j) d
  let I : ℝ := R^2*(Real.pi/4+1/2)
  let K : ℝ := N 0*N 1-2*T*(N 0+N 1)+4*T^2
  have hK : |K| ≤ 1 := abs_central_square_card_correction_le c hT0
  have hH (j : Fin 2) : |H j-I| ≤ 15*Real.sqrt R+4 := by
    have hh := abs_integer_clippedHeight_sum_sub_integral_le (c := c j) hR hT1 hTR hTRle
    dsimp only [T] at hh
    rw [integral_circle_central_excess hRp] at hh
    have hi : Real.pi*R^2/2-R^2*(Real.pi/4-1/2) = I := by
      dsimp only [I]
      ring
    rw [hi] at hh
    exact hh
  have hcount : ((latticeDisc c R).card:ℝ) = N 0*N 1+
      (2*(H 0-T*N 0)-P 0 (c 1)-P 0 (-c 1))+
      (2*(H 1-T*N 1)-P 1 (c 0)-P 1 (-c 0)) := by
    have hh := card_latticeDisc_eq_square_add_cap_sums c hRp.le hT0 hTR
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at hh
    rw [sum_outer_circleHeight_eq_clipped_sub_flat hT0 hTR hTRle,
      sum_outer_circleHeight_eq_clipped_sub_flat hT0 hTR hTRle] at hh
    simpa only [N,H,P,circleCapSawtooth,sub_eq_add_neg] using! hh
  have harea : 4*I-4*T^2 = Real.pi*R^2 := by
    dsimp only [I]
    nlinarith only [hTR]
  have he : ((latticeDisc c R).card:ℝ)-Real.pi*R^2 =
      2*(H 0-I)+2*(H 1-I)+K-P 0 (c 1)-P 0 (-c 1)-P 1 (c 0)-P 1 (-c 0) := by
    dsimp only [K]
    nlinarith only [hcount,harea]
  change |((latticeDisc c R).card:ℝ)-Real.pi*R^2| ≤ 60*Real.sqrt R+17+
    |P 0 (c 1)|+|P 0 (-c 1)|+|P 1 (c 0)|+|P 1 (-c 0)|
  rw [he]
  have h0 := abs_le.mp (hH 0)
  have h1 := abs_le.mp (hH 1)
  have hk := abs_le.mp hK
  apply abs_le.mpr
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,hk.1,hk.2,
    le_abs_self (P 0 (c 1)),neg_abs_le (P 0 (c 1)),
    le_abs_self (P 0 (-c 1)),neg_abs_le (P 0 (-c 1)),
    le_abs_self (P 1 (c 0)),neg_abs_le (P 1 (c 0)),
    le_abs_self (P 1 (-c 0)),neg_abs_le (P 1 (-c 0))]

end WaveTurbulence.Counting
