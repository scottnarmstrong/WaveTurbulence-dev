/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.NumberTheory.Sawtooth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# First-order Euler summation on one lattice cell

The right-continuous sawtooth has the correct midpoint boundary terms
in the Euler summation formula. Its values at the two endpoints do not
affect the integral. This is the local identity underlying sharp Poisson
summation; no Fourier truncation estimate is asserted by this module.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Integration by parts on a unit cell, before introducing the sawtooth. -/
theorem integral_affine_mul_deriv {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F) (a : ℝ) :
    (∫ x in a..a + 1, ((x - a - 1 / 2 : ℝ) : ℂ) * deriv F x) =
      (F (a + 1) + F a) / 2 - ∫ x in a..a + 1, F x := by
  let p : ℝ → ℂ := fun x => (x - a - 1 / 2 : ℝ)
  have hp (x : ℝ) : HasDerivAt p 1 x := by
    simpa only [id_eq, Complex.ofReal_one] using
      (((hasDerivAt_id x).sub_const a).sub_const (1 / 2)).ofReal_comp
  have hpc : Continuous p := Complex.continuous_ofReal.comp
    ((continuous_id.sub continuous_const).sub continuous_const)
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hpc.continuousOn hF.continuous.continuousOn
    (fun x _ => hp x) (fun x _ => (hF.differentiable (by norm_num) x).hasDerivAt)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume a (a + 1))
    (hF.continuous_deriv_one.intervalIntegrable a (a + 1))
  simp only [one_mul] at hh
  convert hh using 1
  dsimp only [p]
  push_cast
  ring

/-- On the interior of an integer cell the sawtooth is the affine
function used in Euler summation. -/
theorem sawtooth_eq_on_cell (n : ℤ) {x : ℝ} (hx : x ∈ Ioo (n : ℝ) ((n : ℝ) + 1)) :
    sawtooth x = x - n - 1 / 2 := by
  have hn : ⌊x⌋ = n := Int.floor_eq_iff.mpr ⟨hx.1.le, hx.2⟩
  rw [sawtooth_eq, hn]

/-- Euler summation on one integer cell, retaining both midpoint terms. -/
theorem integral_sawtooth_mul_deriv_cell {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F) (n : ℤ) :
    (∫ x in (n : ℝ)..(n : ℝ) + 1, (sawtooth x : ℂ) * deriv F x) =
      (F ((n : ℝ) + 1) + F n) / 2 - ∫ x in (n : ℝ)..(n : ℝ) + 1, F x := by
  rw [← integral_affine_mul_deriv hF (n : ℝ)]
  apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
  intro x hx
  dsimp only
  rw [sawtooth_eq_on_cell n hx]

end WaveTurbulence.VdCB
