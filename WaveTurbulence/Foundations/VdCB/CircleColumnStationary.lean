/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleStationary
public import WaveTurbulence.Foundations.VdCB.CircleLatticeDual

/-!
# The circle stationary integral in the original column variable

Reflection retains the factor `e(Rν)`. It cancels the linear part of the
unshifted Legendre phase and produces the actual lattice dual
`R*sqrt(h²+ν²)`.
-/

public section

open MeasureTheory
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Exact reflection formula, retaining the shifted-lattice factor. -/
theorem integral_circleColumnPhase_reflection (R h U ν : ℝ) :
    (∫ x in R - 2 * U..R - U, expPhase (circleColumnPhase R h x + ν * x)) =
      expPhase (R * ν) * ∫ u in U..2 * U, expPhase (circlePhase R h u - ν * u) := by
  have hh := intervalIntegral.integral_comp_sub_left
    (f := fun x => expPhase (circleColumnPhase R h x + ν * x)) (a := U) (b := 2 * U) R
  rw [← hh, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [circleColumnPhase_reflection, ← expPhase_add]
  congr 1
  ring

/-- The reflection factor corrects both the dual phase and its stationary
approximation, without changing the error norm. -/
theorem norm_circleColumnPhase_stationary_error_eq (R h U ν : ℝ) (d : ℂ) :
    ‖(∫ x in R - 2 * U..R - U, expPhase (circleColumnPhase R h x + ν * x)) -
      expPhase (circleLatticeDualPhase R h ν - 1 / 8) / d‖ =
      ‖(∫ u in U..2 * U, expPhase (circlePhase R h u - ν * u)) -
        expPhase (circleDualPhase R h ν - 1 / 8) / d‖ := by
  have hmain : expPhase (circleLatticeDualPhase R h ν - 1 / 8) / d =
      expPhase (R * ν) * (expPhase (circleDualPhase R h ν - 1 / 8) / d) := by
    rw [← mul_div_assoc, ← expPhase_add]
    congr 2
    unfold circleLatticeDualPhase
    ring
  rw [integral_circleColumnPhase_reflection, hmain, ← mul_sub, norm_mul, norm_expPhase, one_mul]

/-- The sharp circle stationary estimate in the original integer-column
variable, with the actual lattice dual phase. -/
theorem norm_integral_circleColumnPhase_sub_main_le {R h U ν r : ℝ}
    (hU : 0 < U) (hUR : 3 * U ≤ R) (hh : 0 < h) (hν : 0 < ν) (hr : 0 < r)
    (ha : U ≤ circleCriticalPoint R h ν - r)
    (hb : circleCriticalPoint R h ν + r ≤ 2 * U) :
    ‖(∫ x in R - 2 * U..R - U, expPhase (circleColumnPhase R h x + ν * x)) -
      expPhase (circleLatticeDualPhase R h ν - 1 / 8) /
        (Real.sqrt (-circleSourceSecond R h (circleCriticalPoint R h ν)) : ℂ)‖ ≤
      2 * Real.pi / 3 * (3 * h * R ^ 3 * (R * U) ^ (-(5 / 2) : ℝ)) * r ^ 4 +
        2 / (Real.pi * ((-circleSourceSecond R h (circleCriticalPoint R h ν)) * r)) +
        2 / (Real.pi * ((h * R ^ 2 * (4 * R * U) ^ (-(3 / 2) : ℝ)) * r)) := by
  rw [norm_circleColumnPhase_stationary_error_eq]
  exact norm_integral_circlePhase_sub_main_le hU hUR hh hν hr ha hb

end WaveTurbulence.VdCB
