/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleQuadrature
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Bounded-slope central circular arc

Subtracting the central excess from a semicircle leaves its height clipped
at the inscribed-square cut. The excess has a uniformly bounded quadrature
error; the square-root error is confined to the original circle tips.
-/

public section

namespace WaveTurbulence.Counting

/-- The central arc lies strictly inside the circle. -/
theorem circle_central_inside {R T c x : ℝ} (hT : 0 < T)
    (hTR : 2*T^2 = R^2) (hx : |x-c| ≤ T) : (x-c)^2 < R^2 := by
  have hs := (sq_le_sq₀ (abs_nonneg _) hT.le).mpr hx
  rw [sq_abs] at hs
  nlinarith only [hs,hTR,sq_pos_of_pos hT]

/-- The central circular height is at least the square half-width. -/
theorem circle_central_height_ge {R T c x : ℝ} (hT : 0 ≤ T)
    (hTR : 2*T^2 = R^2) (hx : |x-c| ≤ T) : T ≤ circleHeight R c x := by
  apply Real.le_sqrt_of_sq_le
  have hs := (sq_le_sq₀ (abs_nonneg _) hT).mpr hx
  rw [sq_abs] at hs
  nlinarith only [hs,hTR]

/-- Both slopes of the central circular arc have absolute value at most one. -/
theorem circle_central_slope_le_one {R T c x : ℝ} (hT : 0 < T)
    (hTR : 2*T^2 = R^2) (hx : |x-c| ≤ T) :
    |-(x-c)/circleHeight R c x| ≤ 1 := by
  have hheight := circle_central_height_ge hT.le hTR hx
  have hp : 0 < circleHeight R c x := hT.trans_le hheight
  rw [abs_div,abs_neg,abs_of_pos hp,div_le_one hp]
  exact hx.trans hheight

/-- The central arc is one-Lipschitz, uniformly in radius and center. -/
theorem abs_circle_central_height_sub_le {R T c x y : ℝ}
    (hT : 0 < T) (hTR : 2*T^2 = R^2)
    (hx : x ∈ Set.Icc (c-T) (c+T)) (hy : y ∈ Set.Icc (c-T) (c+T)) :
    |circleHeight R c y-circleHeight R c x| ≤ |y-x| := by
  have hb (z : ℝ) (hz : z ∈ Set.Icc (c-T) (c+T)) : |z-c| ≤ T :=
    abs_le.mpr ⟨by linarith only [hz.1],by linarith only [hz.2]⟩
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (circleHeight_hasDerivAt (circle_central_inside hT hTR (hb z hz))).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using circle_central_slope_le_one hT hTR (hb z hz))
    (convex_Icc (c-T) (c+T)) hx hy
  simpa only [Real.norm_eq_abs,one_mul] using he

/-- The trapezoidal error for the central arc, after subtracting the square
height, is at most `1/4`, independently of the interval length. -/
theorem abs_circle_central_trapezoid_error_le {R T c a : ℝ} (N : ℕ)
    (hT : 0 < T) (hTR : 2*T^2 = R^2)
    (hl : c-T ≤ a) (hr : a+N ≤ c+T) :
    |(∑ k ∈ Finset.range (N+1), (circleHeight R c (a+k)-T)) -
      ((circleHeight R c a-T)+(circleHeight R c (a+N)-T))/2 -
      (∫ x in a..a+N, (circleHeight R c x-T))| ≤ (1:ℝ)/4 := by
  have hb (x : ℝ) (hx : x ∈ Set.Icc a (a+N)) : |x-c| ≤ T :=
    abs_le.mpr ⟨by linarith only [hl,hx.1],by linarith only [hr,hx.2]⟩
  have hi := fun x hx => circle_central_inside hT hTR (hb x hx)
  have hg := fun x hx => circleHeight_first_hasDerivAt (hi x hx)
  have hj : ContinuousOn (fun x => -(R^2)/circleHeight R c x^3) (Set.Icc a (a+N)) := by
    apply continuousOn_const.div
    · have hc : Continuous (circleHeight R c) := by unfold circleHeight; fun_prop
      exact hc.continuousOn.pow 3
    · intro x hx
      exact pow_ne_zero 3 (circleHeight_pos (hi x hx)).ne'
  have he := abs_trapezoid_sum_sub_integral_le (fun x => circleHeight R c x-T)
    (fun x => -(x-c)/circleHeight R c x) (fun x => -(R^2)/circleHeight R c x^3) a N
    (fun x hx => (circleHeight_hasDerivAt (hi x hx)).sub_const T) hg
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hj
    (fun x hx => div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg R)) (pow_nonneg (Real.sqrt_nonneg _) 3))
  apply he.trans
  have ha := circle_central_slope_le_one hT hTR (hb a ⟨le_rfl,by linarith only [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]⟩)
  have hz := circle_central_slope_le_one hT hTR (hb (a+N) ⟨by linarith only [(Nat.cast_nonneg N : (0:ℝ) ≤ N)],le_rfl⟩)
  have ha' := le_abs_self (-(a-c)/circleHeight R c a)
  have hz' := neg_abs_le (-(a+N-c)/circleHeight R c (a+N))
  linarith only [ha,hz,ha',hz']

end WaveTurbulence.Counting
