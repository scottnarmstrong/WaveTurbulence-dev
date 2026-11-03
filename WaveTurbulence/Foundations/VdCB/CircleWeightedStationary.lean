/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleColumnStationary
public import WaveTurbulence.Foundations.VdCB.CircleCurvature

/-!
# The circle stationary main term with its explicit weight

This is the original-column stationary estimate in the form consumed by
partial summation: explicit decreasing curvature weight times the
corrected lattice-dual character.
-/

public section

open MeasureTheory
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Exact conversion from source curvature to the explicit dual weight. -/
theorem circle_stationary_main_eq_weighted {R h ν : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hν : 0 < ν) (θ : ℝ) :
    expPhase θ / (Real.sqrt (-circleSourceSecond R h (circleCriticalPoint R h ν)) : ℂ) =
      (circleDualWeight R h ν : ℂ) * expPhase θ := by
  have hw : (1 : ℂ) / (Real.sqrt (-circleSourceSecond R h (circleCriticalPoint R h ν)) : ℂ) =
      (circleDualWeight R h ν : ℂ) := by
    exact_mod_cast inv_sqrt_circleSourceSecond_eq_weight hR hh hν
  calc
    _ = expPhase θ * ((1 : ℂ) / (Real.sqrt (-circleSourceSecond R h (circleCriticalPoint R h ν)) : ℂ)) := by ring
    _ = _ := by rw [hw]; ring

/-- Direct circle-family stationary phase with explicit decreasing weight,
without a small-variation premise on the source arc factor. -/
theorem norm_integral_circleColumnPhase_sub_weighted_main_le {R h U ν r : ℝ}
    (hU : 0 < U) (hUR : 3 * U ≤ R) (hh : 0 < h) (hν : 0 < ν) (hr : 0 < r)
    (ha : U ≤ circleCriticalPoint R h ν - r)
    (hb : circleCriticalPoint R h ν + r ≤ 2 * U) :
    ‖(∫ x in R - 2 * U..R - U, expPhase (circleColumnPhase R h x + ν * x)) -
      (circleDualWeight R h ν : ℂ) * expPhase (circleLatticeDualPhase R h ν - 1 / 8)‖ ≤
      2 * Real.pi / 3 * (3 * h * R ^ 3 * (R * U) ^ (-(5 / 2) : ℝ)) * r ^ 4 +
        2 / (Real.pi * ((-circleSourceSecond R h (circleCriticalPoint R h ν)) * r)) +
        2 / (Real.pi * ((h * R ^ 2 * (4 * R * U) ^ (-(3 / 2) : ℝ)) * r)) := by
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  have hhbound := norm_integral_circleColumnPhase_sub_main_le hU hUR hh hν hr ha hb
  rwa [circle_stationary_main_eq_weighted hR hh hν] at hhbound

end WaveTurbulence.VdCB
