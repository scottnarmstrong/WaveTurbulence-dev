/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.GaussianBoundary
public import WaveTurbulence.Foundations.VdCB.Phase
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The positive-curvature Fresnel coefficient

The imaginary Gaussian boundary has coefficient `e(1/8)/sqrt(q)` for
positive curvature `q`. This evaluates the principal complex square-root
branch explicitly, rather than suppressing its sign in a norm estimate.
-/

public section

open MeasureTheory
open WaveTurbulence.NumberTheory
open scoped FourierTransform SchwartzMap

namespace WaveTurbulence.VdCB

/-- The Gaussian square-root branch gives the source phase shift `+1/8`. -/
theorem fresnel_coefficient {q : ℝ} (hq : 0 < q) :
    1 / ((q : ℂ) * (-Complex.I)) ^ (1 / 2 : ℂ) = expPhase (1 / 8) / (Real.sqrt q : ℂ) := by
  have hne : (q : ℂ) * (-Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne') (neg_ne_zero.mpr Complex.I_ne_zero)
  have hs : (Real.sqrt q : ℂ) = Complex.exp ((Real.log q : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hroot : ((q : ℂ) * (-Complex.I)) ^ (1 / 2 : ℂ) =
      (Real.sqrt q : ℂ) * expPhase (-(1 / 8)) := by
    rw [Complex.cpow_def_of_ne_zero hne,
      Complex.log_ofReal_mul hq (neg_ne_zero.mpr Complex.I_ne_zero), Complex.log_neg_I,
      hs, expPhase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hroot, expPhase_neg, one_div, mul_inv, inv_inv, div_eq_mul_inv]
  ring

/-- Exact quadratic Fourier identity for a Schwartz amplitude, including
the Fresnel phase. All integrals here are absolutely integrable because
of the amplitudes, not because of decay of the oscillatory Gaussian. -/
theorem integral_schwartz_mul_quadratic (a : 𝓢(ℝ, ℂ)) {q : ℝ} (hq : 0 < q) :
    (∫ x : ℝ, a x * expPhase (q * x ^ 2 / 2)) =
      (expPhase (1 / 8) / (Real.sqrt q : ℂ)) *
        ∫ ξ : ℝ, 𝓕 a ξ * expPhase (-(ξ ^ 2) / (2 * q)) := by
  have hb : 0 ≤ ((q : ℂ) * (-Complex.I)).re := by simp
  have hbs : (q : ℂ) * (-Complex.I) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.I_re,
      Complex.neg_im, Complex.I_im, mul_zero, add_zero, mul_neg, mul_one] using neg_ne_zero.mpr hq.ne'
  have hh := integral_schwartz_mul_gaussian_closed a hb hbs
  rw [fresnel_coefficient hq] at hh
  have hleft (x : ℝ) : Complex.exp (-Real.pi * ((q : ℂ) * (-Complex.I)) * (x : ℂ) ^ 2) =
      expPhase (q * x ^ 2 / 2) := by
    unfold expPhase
    congr 1
    push_cast
    ring
  have hright (x : ℝ) : Complex.exp (-Real.pi / ((q : ℂ) * (-Complex.I)) * (x : ℂ) ^ 2) =
      expPhase (-(x ^ 2) / (2 * q)) := by
    unfold expPhase
    congr 1
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne', Complex.I_ne_zero]
    simp only [Complex.I_sq]
    ring
  simp_rw [hleft, hright] at hh
  exact hh

end WaveTurbulence.VdCB
