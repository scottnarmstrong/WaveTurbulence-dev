/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.Phase
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Calculus of normalized oscillatory phases

NT-CIRCLE-v2 goal 4: derivative identities for the actual additive character
and its reciprocal-derivative primitive, used in nonstationary integration
by parts and the stationary-phase proof of the B-process.
-/

public section

namespace WaveTurbulence.NumberTheory

open scoped ContDiff

/-- The normalized additive character is smooth as a real-to-complex map. -/
theorem contDiff_expPhase : ContDiff ℝ ∞ expPhase := by
  have hr : ContDiff ℝ ∞ (fun x : ℝ => 2*Real.pi*x) := contDiff_const.mul contDiff_id
  have hc : ContDiff ℝ ∞ (fun x : ℝ => ((2*Real.pi*x:ℝ):ℂ)) := by
    simpa only [Function.comp_apply,Complex.ofRealCLM_apply] using!
      Complex.ofRealCLM.contDiff.comp hr
  exact (hc.mul contDiff_const).cexp

/-- Chain rule for the normalized additive character. -/
theorem hasDerivAt_expPhase_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => expPhase (f y))
      ((2*(Real.pi:ℂ)*Complex.I)*(f':ℂ)*expPhase (f x)) x := by
  have hg := ((hf.const_mul (2*Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  change HasDerivAt (fun y => expPhase (f y))
    (expPhase (f x)*(((2*Real.pi*f':ℝ):ℂ)*Complex.I)) x at hg
  have he : expPhase (f x)*(((2*Real.pi*f':ℝ):ℂ)*Complex.I) =
      (2*(Real.pi:ℂ)*Complex.I)*(f':ℂ)*expPhase (f x) := by push_cast; ring
  rw [he] at hg
  exact hg

/-- The phase derivative at a real point. -/
theorem hasDerivAt_expPhase (x : ℝ) : HasDerivAt expPhase
    ((2*(Real.pi:ℂ)*Complex.I)*expPhase x) x := by
  simpa only [Complex.ofReal_one,mul_one] using!
    hasDerivAt_expPhase_comp (hasDerivAt_id x)

/-- The fixed complex frequency factor is nonzero. -/
theorem two_pi_mul_I_ne_zero : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- Derivative of the reciprocal-derivative phase primitive. -/
theorem hasDerivAt_expPhase_div_deriv {f g : ℝ → ℝ} {g' x : ℝ}
    (hf : HasDerivAt f (g x) x) (hg : HasDerivAt g g' x) (hne : g x ≠ 0) :
    HasDerivAt (fun y => expPhase (f y)/((2*(Real.pi:ℂ)*Complex.I)*(g y:ℂ)))
      (expPhase (f x)-expPhase (f x)*(g':ℂ)/
        ((2*(Real.pi:ℂ)*Complex.I)*(g x:ℂ)^2)) x := by
  have hden := hg.ofReal_comp.const_mul (2*(Real.pi:ℂ)*Complex.I)
  have hn : ((2*(Real.pi:ℂ)*Complex.I)*(g x:ℂ)) ≠ 0 :=
    mul_ne_zero two_pi_mul_I_ne_zero (Complex.ofReal_ne_zero.mpr hne)
  have hd := (hasDerivAt_expPhase_comp hf).div hden hn
  have he :
      (((2*(Real.pi:ℂ)*Complex.I)*(g x:ℂ)*expPhase (f x))*
        ((2*(Real.pi:ℂ)*Complex.I)*(g x:ℂ))-
        expPhase (f x)*((2*(Real.pi:ℂ)*Complex.I)*(g':ℂ)))/
        ((2*(Real.pi:ℂ)*Complex.I)*(g x:ℂ))^2 =
      expPhase (f x)-expPhase (f x)*(g':ℂ)/
        ((2*(Real.pi:ℂ)*Complex.I)*(g x:ℂ)^2) := by
    field_simp [two_pi_mul_I_ne_zero,Complex.ofReal_ne_zero.mpr hne]
  rw [he] at hd
  exact hd

end WaveTurbulence.NumberTheory
