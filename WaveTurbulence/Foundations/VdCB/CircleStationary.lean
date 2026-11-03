/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleLocalization
public import WaveTurbulence.Foundations.VdCB.CircleSourceBounds
public import WaveTurbulence.Foundations.VdCB.SharpStationaryNegative
public import WaveTurbulence.Foundations.VdCB.StationarySum

/-!
# Sharp stationary phase for the actual circle family

The smooth localization is used only as an internal representative.
The theorem's integral, critical equation, curvature and Legendre phase
all refer to the original circle source phase.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory
open scoped ContDiff

namespace WaveTurbulence.VdCB

/-- Explicit stationary-phase estimate for a dyadic circle block. This
covers the full O(1) multiplicative arc factor without a smallness premise. -/
theorem norm_integral_circlePhase_sub_main_le {R h U ν r : ℝ}
    (hU : 0 < U) (hUR : 3 * U ≤ R) (hh : 0 < h) (hν : 0 < ν) (hr : 0 < r)
    (ha : U ≤ circleCriticalPoint R h ν - r)
    (hb : circleCriticalPoint R h ν + r ≤ 2 * U) :
    ‖(∫ x in U..2 * U, expPhase (circlePhase R h x - ν * x)) -
      expPhase (circleDualPhase R h ν - 1 / 8) /
        (Real.sqrt (-circleSourceSecond R h (circleCriticalPoint R h ν)) : ℂ)‖ ≤
      2 * Real.pi / 3 * (3 * h * R ^ 3 * (R * U) ^ (-(5 / 2) : ℝ)) * r ^ 4 +
        2 / (Real.pi * ((-circleSourceSecond R h (circleCriticalPoint R h ν)) * r)) +
        2 / (Real.pi * ((h * R ^ 2 * (4 * R * U) ^ (-(3 / 2) : ℝ)) * r)) := by
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  let F := circleSourceExtension R h U hU
  let c := circleCriticalPoint R h ν
  have hcI : c ∈ Icc U (2 * U) := ⟨by dsimp only [c]; linarith, by dsimp only [c]; linarith⟩
  have hF : ContDiff ℝ 3 F := (contDiff_circleSourceExtension hU hUR h).of_le (by simp)
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hd := hF2.differentiable (by norm_num)
  have hderiv2 (x : ℝ) (hx : x ∈ Icc U (2 * U)) :
      deriv (deriv F) x = circleSourceSecond R h x := by
    have heq := iteratedDeriv_circleSourceExtension (R := R) (h := h) hU hx 2
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at heq
    rw [heq]
    exact deriv_deriv_circlePhase hR ⟨hU.trans_le hx.1, by linarith [hx.2]⟩
  have hcrit : deriv F c = ν := by
    rw [(circleSourceExtension_eventuallyEq (R := R) (h := h) hU hcI).deriv_eq]
    exact (hasDerivAt_circlePhase_critical hR hh hν).deriv
  have hμ : 0 < h * R ^ 2 * (4 * R * U) ^ (-(3 / 2) : ℝ) := by positivity
  have hM0 : 0 ≤ 3 * h * R ^ 3 * (R * U) ^ (-(5 / 2) : ℝ) := by positivity
  have hstat := norm_integral_stationary_neg_sub_main_le
    (f := fun x => F x - ν * x) (hF.sub (contDiff_const.mul contDiff_id)) hr hμ ha hb
    (by rw [deriv_sub_frequency hd, hcrit, sub_self])
    (by
      intro x hx
      rw [deriv_deriv_sub_frequency hF2, hderiv2 x hx]
      have hbnd := (neg_deriv_deriv_circlePhase_bounds hU hUR hh hx).1
      rw [deriv_deriv_circlePhase hR ⟨hU.trans_le hx.1, by linarith [hx.2]⟩] at hbnd
      linarith only [hbnd]) hM0
    (by
      intro x hx
      have hxI : x ∈ Icc U (2 * U) := ⟨ha.trans hx.1, hx.2.trans hb⟩
      rw [iteratedDeriv_three_sub_frequency hF2,
        iteratedDeriv_circleSourceExtension hU hxI]
      exact abs_iteratedDeriv_three_circlePhase_le hU hUR hh hxI)
  simp only [deriv_deriv_sub_frequency hF2] at hstat
  rw [hderiv2 (circleCriticalPoint R h ν) hcI] at hstat
  have hFc : F c = circlePhase R h c :=
    (circleSourceExtension_eventuallyEq (R := R) (h := h) hU hcI).eq_of_nhds
  rw [hFc, circlePhase_sub_frequency_eq_dual hR hh] at hstat
  have heq : (∫ x in U..2 * U, expPhase (F x - ν * x)) =
      ∫ x in U..2 * U, expPhase (circlePhase R h x - ν * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : U ≤ 2 * U)] at hx
    dsimp only [F]
    rw [(circleSourceExtension_eventuallyEq (R := R) (h := h) hU hx).eq_of_nhds]
  rw [heq] at hstat
  exact hstat

end WaveTurbulence.VdCB
