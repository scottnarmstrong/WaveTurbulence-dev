/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleLegendre
public import WaveTurbulence.Foundations.VdCB.CircleDualBounds
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The dual phase for the original integer circle columns

The substitution `u=R-n` gives the shifted lattice `R-ℤ`, not `ℤ` unless
`R` is integral. Its Poisson factor cancels the linear term in the `u`
Legendre phase. The actual integer-column dual is `R sqrt(h²+ν²)`.
Its fifth derivative is unchanged and retains the uniform bounds.
-/

public section

namespace WaveTurbulence.VdCB

/-- Circle phase on the original integer column variable. -/
@[expose] noncomputable def circleColumnPhase (R h x : ℝ) : ℝ := h * Real.sqrt (R ^ 2 - x ^ 2)

/-- The dual phase after retaining the shifted-lattice Poisson factor. -/
@[expose] noncomputable def circleLatticeDualPhase (R h x : ℝ) : ℝ := circleDualPhase R h x + R * x

theorem circleLatticeDualPhase_eq (R h x : ℝ) :
    circleLatticeDualPhase R h x = R * Real.sqrt (h ^ 2 + x ^ 2) := by
  unfold circleLatticeDualPhase circleDualPhase
  rw [← Real.sqrt_eq_rpow]
  ring

theorem circleColumnPhase_reflection (R h u : ℝ) :
    circleColumnPhase R h (R - u) = circlePhase R h u := by
  unfold circleColumnPhase circlePhase
  rw [show R ^ 2 - (R - u) ^ 2 = 2 * R * u - u ^ 2 by ring]

/-- Exact stationary value for the original integer-column phase. -/
theorem circleColumnPhase_add_frequency_eq_dual {R h ν : ℝ} (hR : 0 < R) (hh : 0 < h) :
    circleColumnPhase R h (R - circleCriticalPoint R h ν) + ν * (R - circleCriticalPoint R h ν) =
      circleLatticeDualPhase R h ν := by
  rw [circleColumnPhase_reflection]
  have hp := circlePhase_sub_frequency_eq_dual hR hh (ν := ν)
  unfold circleLatticeDualPhase
  linear_combination hp

/-- The linear shifted-lattice correction changes no fifth derivative. -/
theorem iteratedDeriv_five_circleLatticeDualPhase (R : ℝ) {h : ℝ} (hh : 0 < h) :
    iteratedDeriv 5 (circleLatticeDualPhase R h) = circleDualFifth R h := by
  have h1 : deriv (circleLatticeDualPhase R h) = fun x => circleDualFirst R h x + R := by
    funext x
    have hp : HasDerivAt (circleLatticeDualPhase R h) (circleDualFirst R h x + R) x := by
      convert (hasDerivAt_circleDualPhase R hh x).add ((hasDerivAt_id x).const_mul R) using 1
      · funext y
        rfl
      · rw [mul_one]
    exact hp.deriv
  have h2 : deriv (fun x => circleDualFirst R h x + R) = circleDualSecond R h := by
    funext x
    exact ((hasDerivAt_circleDualFirst R hh x).add_const R).deriv
  have h3 : deriv (circleDualSecond R h) = circleDualThird R h :=
    funext fun x => (hasDerivAt_circleDualSecond R hh x).deriv
  have h4 : deriv (circleDualThird R h) = circleDualFourth R h :=
    funext fun x => (hasDerivAt_circleDualThird R hh x).deriv
  have h5 : deriv (circleDualFourth R h) = circleDualFifth R h :=
    funext fun x => (hasDerivAt_circleDualFourth R hh x).deriv
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, h1, h2, h3, h4, h5]

/-- Uniform fifth-derivative comparability for the actual integer-column dual. -/
theorem abs_iteratedDeriv_five_circleLatticeDualPhase_bounds {R h Y x : ℝ} (hR : 0 < R)
    (hh : 0 < h) (hY : h ≤ Y) (hx : x ∈ Set.Icc Y (2 * Y)) :
    R * h ^ 2 / (125 * Y ^ 6) ≤ |iteratedDeriv 5 (circleLatticeDualPhase R h) x| ∧
      |iteratedDeriv 5 (circleLatticeDualPhase R h) x| ≤ 480 * R * h ^ 2 / Y ^ 6 := by
  simpa only [iteratedDeriv_five_circleLatticeDualPhase R hh, iteratedDeriv_five_circleDualPhase R hh] using
    abs_iteratedDeriv_five_circleDualPhase_bounds hR hh hY hx

end WaveTurbulence.VdCB
