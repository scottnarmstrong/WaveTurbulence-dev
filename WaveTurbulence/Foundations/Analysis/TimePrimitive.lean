/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.OscillatoryInterval
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Linear

/-!
# Smooth oscillatory primitives

The primitives used by the cutoff time-integration operator. Frequencies
here use Fourier normalization `2π`; DH21's phase `παt` corresponds to `α/2`.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Analysis

/-- The Fourier-normalized oscillatory exponential. -/
@[expose] noncomputable def timePhase (q t : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * q * t : ℝ) * Complex.I)

/-- The primitive based at `a`. It is defined at every real upper endpoint,
including endpoints smaller than `a`. -/
@[expose] noncomputable def timePrimitive (a q t : ℝ) : ℂ := ∫ s in a..t, timePhase q s

theorem contDiff_timePhase (q : ℝ) : ContDiff ℝ ∞ (timePhase q) := by
  have hco : ContDiff ℝ ∞ (fun t : ℝ => (2 * Real.pi * q * t : ℝ)) :=
    contDiff_const.mul contDiff_id
  have hc := Complex.ofRealCLM.contDiff.comp hco
  exact (hc.mul contDiff_const).cexp

theorem norm_timePhase (q t : ℝ) : ‖timePhase q t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_timePrimitive (a q t : ℝ) :
    HasDerivAt (timePrimitive a q) (timePhase q t) t :=
  ((contDiff_timePhase q).continuous.integral_hasStrictDerivAt a t).hasDerivAt

theorem deriv_timePrimitive (a q t : ℝ) : deriv (timePrimitive a q) t = timePhase q t :=
  (hasDerivAt_timePrimitive a q t).deriv

theorem contDiff_timePrimitive (a q : ℝ) : ContDiff ℝ ∞ (timePrimitive a q) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (hasDerivAt_timePrimitive a q t).differentiableAt, ?_⟩
  have heq : deriv (timePrimitive a q) = timePhase q := funext (deriv_timePrimitive a q)
  rw [heq]
  exact contDiff_timePhase q

/-- The primitive is bounded by the length of its interval. -/
theorem norm_timePrimitive_le (a q t : ℝ) : ‖timePrimitive a q t‖ ≤ |t - a| := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := t) (C := 1) (fun s _ => (norm_timePhase q s).le)
  simpa only [timePrimitive, one_mul] using hh

/-- The first derivative of the Fourier-normalized phase. -/
theorem hasDerivAt_timePhase (q t : ℝ) :
    HasDerivAt (timePhase q) ((2 * Real.pi * q : ℂ) * Complex.I * timePhase q t) t := by
  have hlin : HasDerivAt (fun s : ℝ => 2 * Real.pi * q * s) (2 * Real.pi * q) t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (2 * Real.pi * q)
  have hco := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hlin
  have hh := (hco.mul_const Complex.I).cexp
  convert hh using 1
  · funext s
    rfl
  · simp only [Function.comp_apply, Complex.ofRealCLM_apply, timePhase]
    push_cast
    ring

end WaveTurbulence.Analysis
