/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.ExponentAudit
import Mathlib.Tactic

/-!
# Numerical audit for the proposed exponent 35/53

These are numerical comparisons of the source annulus branches. They do
not assert that an exponent pair or an improved circle estimate is proved.
-/

public section

namespace WaveTurbulence.Counting

/-- Exact scalar arithmetic for the proposed `BAABAAB` chain. This does
not assert the analytic closure of either exponent-pair transformation. -/
theorem exponent_coordinate_chain_BAABAAB :
    let A : ℝ × ℝ → ℝ × ℝ := fun p =>
      (p.1/(2*p.1+2),(p.1+p.2+1)/(2*p.1+2))
    let B : ℝ × ℝ → ℝ × ℝ := fun p => (p.2-1/2,p.1+1/2)
    B (A (A (B (A (A (B (0,1))))))) = ((13:ℝ)/40,(11:ℝ)/20) := by
  norm_num

/-- The orchestrator's proposed pair gives the circle exponent `35/53`. -/
theorem circle_exponent_thirteen_fortieths :
    (((13:ℝ)/40)+11/20)/(1+13/40) = (35:ℝ)/53 := by norm_num

/-- The strict improvement over two thirds is exactly `1/159`. -/
theorem circle_exponent_thirty_five_fifty_thirds_gap :
    (2:ℝ)/3-35/53 = 1/159 := by norm_num

/-- DH23 L2082 with all three elementary terms retained: the branch split
is `q = 477/395`, giving exponent `63/79 = 4/5-1/395`. -/
theorem annulus_thirty_five_fifty_thirds_exponent_le (q : ℝ) :
    min (max ((2:ℝ)/5) (35*q/53))
      (max ((1:ℝ)/5) (max (8/5-q) (6/5-q/3))) ≤ (63:ℝ)/79 := by
  by_cases hq : q ≤ (477:ℝ)/395
  · apply (min_le_left _ _).trans
    apply max_le <;> linarith only [hq]
  · apply (min_le_right _ _).trans
    apply max_le
    · norm_num
    · apply max_le <;> linarith only [hq]

/-- The saving at the critical gamma is larger than the source's fixed
`1/10000` margin. This comparison concerns powers, before implicit constants. -/
theorem annulus_thirty_five_fifty_thirds_saving :
    (63:ℝ)/79 = 4/5-1/395 ∧ (1:ℝ)/10000 < 1/395 := by norm_num

/-- Every smaller nonnegative circle exponent retains the previously
proved comparisons for DH23 `basiccount0` (1) and (3), when `Q >= 1`. -/
theorem annulus_exponent_le_of_le_two_thirds {e γ q : ℝ}
    (he : e ≤ (2:ℝ)/3) (hq : 0 ≤ q) (hγ : (1:ℝ)/2 ≤ γ) :
    min (max (2-2*γ) (e*q))
      (max (1-γ) (max (4-3*γ-q) (2-γ-q/3))) ≤ (4-2*γ)/3 := by
  apply le_trans (min_le_min (max_le_max le_rfl ?_) le_rfl)
    (annulus_two_thirds_exponent_le hγ)
  nlinarith only [mul_le_mul_of_nonneg_right he hq]

/-- The improved exponent preserves the exact fixed saving claimed in
DH23 L2077 and L2088, including gamma arbitrarily close to one half. -/
theorem annulus_thirty_five_fifty_thirds_source_saving {γ q : ℝ}
    (hγ : (1:ℝ)/2 ≤ γ) :
    min (max (2-2*γ) (35*q/53))
      (max (1-γ) (max (4-3*γ-q) (2-γ-q/3))) ≤
        1-min ((1:ℝ)/1000) (2*γ-1) := by
  have hm1 := min_le_left ((1:ℝ)/1000) (2*γ-1)
  have hm2 := min_le_right ((1:ℝ)/1000) (2*γ-1)
  by_cases hq : q ≤ 159*(2-γ)/158
  · apply (min_le_left _ _).trans
    apply max_le
    · linarith only [hm2]
    · linarith only [hγ,hq,hm1]
  · apply (min_le_right _ _).trans
    apply max_le
    · linarith only [hγ,hm1]
    · apply max_le <;> linarith only [hγ,hq,hm1]

/-- Explicit room for the source's unspecified `O(eta)` losses near its
critical gamma. For any fixed loss coefficient, eta can be chosen small
enough to preserve the required `20*eta` saving. -/
theorem annulus_thirty_five_fifty_thirds_eta_margin {γ η D : ℝ}
    (hγ : (4:ℝ)/5-10*η ≤ γ) (hsmall : (D+30)*η ≤ (1:ℝ)/395) :
    (63:ℝ)/79+D*η ≤ γ-20*η := by
  nlinarith only [hγ,hsmall]

end WaveTurbulence.Counting
