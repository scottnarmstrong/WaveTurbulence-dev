/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Four Cartesian charts for a thin annulus

Every point of the annulus of radius `Q` and half-width `rho ≤ Q/2` lies
in one of four charts with a signed coordinate at least `Q/4`.
-/

public section

namespace WaveTurbulence.Counting

/-- Each Cartesian coordinate is bounded by twice the radius in an annulus
whose half-width is at most its radius. -/
theorem annulus_abs_coordinates_le {x y Q rho : ℝ} (hrhoQ : rho ≤ Q)
    (hann : |Real.sqrt (x^2+y^2)-Q| ≤ rho) : |x| ≤ 2*Q ∧ |y| ≤ 2*Q := by
  have hnorm : Real.sqrt (x^2+y^2) ≤ Q+rho := by
    have hh := (abs_le.mp hann).2
    linarith only [hh]
  have hx : |x| ≤ Real.sqrt (x^2+y^2) := by
    apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
    rw [sq_abs]
    linarith only [sq_nonneg y]
  have hy : |y| ≤ Real.sqrt (x^2+y^2) := by
    apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
    rw [sq_abs]
    linarith only [sq_nonneg x]
  constructor <;> linarith only [hx,hy,hnorm,hrhoQ]

/-- The four upper, right, lower and left charts cover the entire thin
annulus. In particular there is no uncovered angular boundary. -/
theorem annulus_mem_four_charts {x y Q rho : ℝ} (hQ : 0 < Q) (hrhoQ : rho ≤ Q/2)
    (hann : |Real.sqrt (x^2+y^2)-Q| ≤ rho) :
    Q/4 ≤ y ∨ Q/4 ≤ x ∨ Q/4 ≤ -y ∨ Q/4 ≤ -x := by
  have hlo : Q/2 ≤ Real.sqrt (x^2+y^2) := by
    have hh := (abs_le.mp hann).1
    linarith only [hh,hrhoQ]
  by_contra h
  push Not at h
  have hax : |x| ≤ Q/4 := abs_le.mpr ⟨by linarith only [h.2.2.2],h.2.1.le⟩
  have hay : |y| ≤ Q/4 := abs_le.mpr ⟨by linarith only [h.2.2.1],h.1.le⟩
  have hxsq := pow_le_pow_left₀ (abs_nonneg _) hax 2
  have hysq := pow_le_pow_left₀ (abs_nonneg _) hay 2
  rw [sq_abs] at hxsq hysq
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ Q/2) hlo 2
  rw [Real.sq_sqrt (by positivity)] at hsq
  nlinarith only [hxsq,hysq,hsq,sq_pos_of_pos hQ]

end WaveTurbulence.Counting
