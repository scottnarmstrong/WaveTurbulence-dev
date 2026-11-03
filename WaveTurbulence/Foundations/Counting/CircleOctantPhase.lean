/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleArc
import Mathlib.Tactic

/-!
# Power profile of the circular octant

On the outer octant, distance `u` from the horizontal endpoint gives the
square-root power profile with factor `sqrt (1-u/(2R))`. This module only
records actual geometric identities and regularity; the exponent-pair API
belongs to `Foundations/VdCB`.
-/

public section

namespace WaveTurbulence.Counting

/-- Smooth factor in the circular endpoint's square-root power profile. -/
@[expose] noncomputable def circleEndpointFactor (t : ℝ) : ℝ :=
  Real.sqrt (1-t/2)

/-- The endpoint factor stays bounded above and away from zero on `[0,1]`.
The octant only uses the smaller interval `[0,1-1/sqrt 2]`. -/
theorem circleEndpointFactor_bounds {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    circleEndpointFactor t ∈ Set.Icc (1/2:ℝ) 1 := by
  have hb : 0 ≤ 1-t/2 := by linarith only [ht.2]
  have hs := Real.sq_sqrt hb
  have hn := Real.sqrt_nonneg (1-t/2)
  change 1/2 ≤ Real.sqrt (1-t/2) ∧ Real.sqrt (1-t/2) ≤ 1
  constructor <;> nlinarith only [ht.1,ht.2,hs,hn]

/-- The profile factor is smooth of every finite order on `t < 2`. -/
theorem circleEndpointFactor_contDiffOn (m : ℕ) :
    ContDiffOn ℝ m circleEndpointFactor (Set.Iio 2) := by
  have h : ContDiff ℝ m (fun t : ℝ => 1-t/2) :=
    contDiff_const.sub (contDiff_id.div_const 2)
  apply h.contDiffOn.sqrt
  intro t ht
  have ht' : t < 2 := ht
  exact ne_of_gt (by linarith only [ht'])

/-- Exact endpoint power profile, including the endpoint `u=0`, uniformly
in the horizontal center. -/
theorem circleHeight_endpoint_profile {R : ℝ} (hR : 0 < R) (c u : ℝ) (hu : 0 ≤ u) :
    circleHeight R c (c+R-u) =
      Real.sqrt (2*R)*Real.sqrt u*circleEndpointFactor (u/R) := by
  unfold circleHeight circleEndpointFactor
  have he : R^2-(c+R-u-c)^2 = (2*R)*u*(1-(u/R)/2) := by
    field_simp
    ring
  rw [he,Real.sqrt_mul (by positivity : 0 ≤ (2*R)*u)]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2*R)]

/-- The left endpoint has the same profile after reflection, for arbitrary
horizontal center. -/
theorem circleHeight_left_endpoint_profile {R : ℝ} (hR : 0 < R)
    (c u : ℝ) (hu : 0 ≤ u) :
    circleHeight R c (c-R+u) =
      Real.sqrt (2*R)*Real.sqrt u*circleEndpointFactor (u/R) := by
  have he : circleHeight R c (c-R+u) = circleHeight R c (c+R-u) := by
    unfold circleHeight
    congr 1
    ring
  rw [he,circleHeight_endpoint_profile hR c u hu]

/-- Every outer-octant coordinate has endpoint distance in `[0,R]`.
The sharper octant upper bound is not needed for the profile factor bounds. -/
theorem circle_octant_endpoint_distance {R x : ℝ} (hR : 0 < R)
    (hx : R/Real.sqrt 2 ≤ x) (hxR : x ≤ R) :
    R-x ∈ Set.Icc (0:ℝ) R := by
  have hx0 : 0 ≤ x := (by positivity : 0 ≤ R/Real.sqrt 2).trans hx
  constructor <;> linarith only [hxR,hx0]

end WaveTurbulence.Counting
