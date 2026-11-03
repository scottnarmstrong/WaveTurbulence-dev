/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleCapCounting
public import WaveTurbulence.Foundations.Counting.CircleClippedHeight
public import WaveTurbulence.Foundations.Counting.LatticeCoordinateSwap
import Mathlib.Tactic

/-!
# Exact translated circle count using outer octants

The central rectangle and the four outer caps give an exact finite formula.
Clipped heights absorb the central rectangle's terms of order the radius,
leaving only a bounded square correction and outer-octant sawtooth sums.
-/

public section

namespace WaveTurbulence.Counting

/-- Exact square-plus-caps formula with both coordinate directions written
in their original coordinates. Every circular boundary remains closed. -/
theorem card_latticeDisc_eq_square_add_cap_sums
    (c : EuclideanSpace ℝ (Fin 2)) {R T : ℝ}
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hTR : 2*T^2 = R^2) :
    ((latticeDisc c R).card:ℝ) =
      ((integerInterval (c 0-T) (c 0+T)).card:ℝ)*
        ((integerInterval (c 1-T) (c 1+T)).card:ℝ)+
      (∑ x ∈ (integerInterval (c 0-R) (c 0+R)).filter (fun x : ℤ => T < |(x:ℝ)-c 0|),
        (2*circleHeight R (c 0) x-NumberTheory.sawtooth (circleHeight R (c 0) x+c 1)-
          NumberTheory.sawtooth (circleHeight R (c 0) x-c 1)))+
      (∑ y ∈ (integerInterval (c 1-R) (c 1+R)).filter (fun y : ℤ => T < |(y:ℝ)-c 1|),
        (2*circleHeight R (c 1) y-NumberTheory.sawtooth (circleHeight R (c 1) y+c 0)-
          NumberTheory.sawtooth (circleHeight R (c 1) y-c 0))) := by
  classical
  have he := congrArg (fun n : ℕ => (n:ℝ)) (card_latticeDisc_eq_square_add_caps c hR hT hTR)
  rw [card_latticeDisc_central_square c hR hT hTR,
    card_latticeDisc_horizontal_caps_eq_swap c hR T] at he
  push_cast at he
  rw [card_latticeDisc_vertical_caps_eq,card_latticeDisc_vertical_caps_eq] at he
  simpa only [planeSwapCenter,WithLp.ofLp_toLp,Matrix.cons_val_zero,Matrix.cons_val_one] using! he

/-- The two cap height sums are precisely the clipped sum minus its flat
central rectangle contribution. -/
theorem sum_outer_circleHeight_eq_clipped_sub_flat {R T c : ℝ}
    (hT : 0 ≤ T) (hTR : 2*T^2 = R^2) (hTRle : T ≤ R) :
    (∑ x ∈ (integerInterval (c-R) (c+R)).filter (fun x : ℤ => T < |(x:ℝ)-c|),
      circleHeight R c x) =
      (∑ x ∈ integerInterval (c-R) (c+R), circleClippedHeight R T c x)-
      T*((integerInterval (c-T) (c+T)).card:ℝ) := by
  classical
  have he : (integerInterval (c-R) (c+R)).filter (fun x : ℤ => |(x:ℝ)-c| ≤ T) =
      integerInterval (c-T) (c+T) := by
    ext x
    simp only [Finset.mem_filter,mem_integerInterval,abs_le]
    constructor
    · rintro ⟨_,hx1,hx2⟩
      constructor <;> linarith only [hx1,hx2]
    · rintro ⟨hx1,hx2⟩
      constructor
      · constructor <;> linarith only [hx1,hx2,hTRle]
      · constructor <;> linarith only [hx1,hx2]
  have hs := Finset.sum_filter_add_sum_filter_not (integerInterval (c-R) (c+R))
    (fun x : ℤ => |(x:ℝ)-c| ≤ T) (fun x => circleHeight R c x)
  simp only [not_le,he] at hs
  rw [sum_circleClippedHeight_eq hT hTR hTRle,Finset.sum_sub_distrib,
    Finset.sum_const,nsmul_eq_mul]
  linarith only [hs]

end WaveTurbulence.Counting
