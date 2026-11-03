/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.NumberTheory.Phase
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Phase calculus for van der Corput's B-process

The additive character is the landed `NumberTheory.expPhase`, namely
`e(t)=exp(2πit)`. No second copy of the phase convention is introduced.
-/

public section

open MeasureTheory
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Chain rule for the normalized additive character. -/
theorem hasDerivAt_expPhase_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => expPhase (f t))
      ((2 * Real.pi : ℂ) * Complex.I * (f' : ℂ) * expPhase (f x)) x := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hf.const_mul (2 * Real.pi))
  have hh := (hc.mul_const Complex.I).cexp
  convert hh using 1
  · funext t
    rfl
  · simp only [Function.comp_apply, Complex.ofRealCLM_apply, expPhase]
    push_cast
    ring

/-- The normalized phase is smooth as a real-to-complex function. -/
theorem contDiff_expPhase (n : WithTop ℕ∞) : ContDiff ℝ n expPhase := by
  have hc := Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id :
    ContDiff ℝ n (fun x : ℝ => 2 * Real.pi * x))
  exact (hc.mul contDiff_const).cexp

/-- Lipschitz control used to compare a phase with its Taylor polynomial. -/
theorem norm_expPhase_sub_le (x y : ℝ) : ‖expPhase x - expPhase y‖ ≤ 2 * Real.pi * |x - y| := by
  have heq : expPhase x - expPhase y = expPhase y * (expPhase (x - y) - 1) := by
    rw [mul_sub, ← expPhase_add, add_sub_cancel, mul_one]
  rw [heq, norm_mul, norm_expPhase, one_mul]
  have hp : expPhase (x - y) = Complex.exp (Complex.I * (2 * Real.pi * (x - y) : ℝ)) := by
    unfold expPhase
    congr 1
    ring
  rw [hp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hs := Real.abs_sin_le_abs (x := 2 * Real.pi * (x - y) / 2)
  calc
    _ ≤ 2 * |2 * Real.pi * (x - y) / 2| := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by
      rw [show 2 * Real.pi * (x - y) / 2 = Real.pi * (x - y) by ring,
        abs_mul, abs_of_pos Real.pi_pos]
      ring

/-- The trivial interval-length estimate for a normalized oscillatory integral. -/
theorem norm_integral_expPhase_le {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    ‖∫ x in a..b, expPhase (f x)‖ ≤ b - a := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
    (fun x _ => (norm_expPhase (f x)).le)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab), one_mul] using hh

end WaveTurbulence.VdCB
