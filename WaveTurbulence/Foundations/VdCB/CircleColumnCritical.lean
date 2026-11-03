/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleColumnLocalization
public import WaveTurbulence.Foundations.VdCB.CircleCriticalUniqueness
public import WaveTurbulence.Foundations.VdCB.CircleWeightedStationary

/-!
# Actual translated-column critical points and stationary main terms

Any critical point selected by the generic B-process is identified with
the explicit circle point. Its actual main term is the decreasing dual
weight times the corrected dual phase, including the real-center shift.
-/

public section

open Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- An actual column stationary equation determines the explicit point. -/
theorem circleColumnExtension_critical_eq {R h U c x ν : ℝ}
    (hU : 0 < U) (hUR : 3 * U ≤ R) (hh : 0 < h) (hν : 0 < ν)
    (hx : R + c - x ∈ Icc U (2 * U))
    (hcritical : deriv (circleColumnExtension R h U hU c) x = -ν) :
    R + c - x = circleCriticalPoint R h ν := by
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  rw [deriv_circleColumnExtension hU hR hx hUR] at hcritical
  apply eq_circleCriticalPoint_of_sourceFirst_eq hR hh hν
    ⟨hU.trans_le hx.1, by linarith [hx.2]⟩
  linarith only [hcritical]

/-- The actual localized stationary value is the corrected lattice dual
plus its unavoidable real-center linear phase. -/
theorem circleColumnExtension_stationary_value {R h U c x ν : ℝ}
    (hU : 0 < U) (hUR : 3 * U ≤ R) (hh : 0 < h) (hν : 0 < ν)
    (hx : R + c - x ∈ Icc U (2 * U))
    (hcritical : deriv (circleColumnExtension R h U hU c) x = -ν) :
    circleColumnExtension R h U hU c x + ν * x = circleLatticeDualPhase R h ν + c * ν := by
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  have hpoint := circleColumnExtension_critical_eq hU hUR hh hν hx hcritical
  have hxcol : x - c = R - circleCriticalPoint R h ν := by linarith only [hpoint]
  have hphase := (circleColumnExtension_eventuallyEq (R := R) (h := h) (c := c) hU hx).eq_of_nhds
  rw [hphase, hxcol]
  have hleg := circleColumnPhase_add_frequency_eq_dual hR hh (ν := ν)
  linear_combination hleg - ν * hpoint

/-- The selected stationary main term has its explicit weight and phase,
with no dependence on the choice made by intermediate value. -/
theorem circleColumnExtension_stationary_main {R h U c x ν : ℝ}
    (hU : 0 < U) (hUR : 3 * U ≤ R) (hh : 0 < h) (hν : 0 < ν)
    (hx : R + c - x ∈ Icc U (2 * U))
    (hcritical : deriv (circleColumnExtension R h U hU c) x = -ν) :
    expPhase (circleColumnExtension R h U hU c x + ν * x - 1 / 8) /
      (Real.sqrt (-deriv (deriv (circleColumnExtension R h U hU c)) x) : ℂ) =
        (circleDualWeight R h ν : ℂ) * expPhase (circleLatticeDualPhase R h ν + c * ν - 1 / 8) := by
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  have hpoint := circleColumnExtension_critical_eq hU hUR hh hν hx hcritical
  rw [circleColumnExtension_stationary_value hU hUR hh hν hx hcritical,
    deriv_deriv_circleColumnExtension hU hR hx hUR, hpoint]
  exact circle_stationary_main_eq_weighted hR hh hν _

end WaveTurbulence.VdCB
