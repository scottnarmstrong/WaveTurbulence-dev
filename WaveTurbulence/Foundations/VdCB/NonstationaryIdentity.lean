/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The exact nonstationary phase identity

Outside the derivative range, division by the actual derivative gives
an endpoint term and a remainder with an integrable squared denominator.
This is the identity before taking absolute values or pairing frequencies.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Exact integration by parts when the phase derivative has no zero on
the interval. The two derivative functions in the formula are actual
Lean derivatives of the phase, not supplied analytic inputs. -/
theorem integral_expPhase_nonstationary {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b : ℝ}
    (hne : ∀ x ∈ uIcc a b, deriv f x ≠ 0) :
    (∫ x in a..b, expPhase (f x)) =
      (expPhase (f b) * ((deriv f b)⁻¹ : ℝ) - expPhase (f a) * ((deriv f a)⁻¹ : ℝ) -
        ∫ x in a..b, expPhase (f x) * (-(deriv (deriv f) x) / (deriv f x) ^ 2 : ℝ)) /
          ((2 * Real.pi : ℂ) * Complex.I) := by
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hf0 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf1d : Differentiable ℝ (deriv f) := hf1.differentiable (by norm_num)
  have hfc : ContinuousOn (deriv f) (uIcc a b) := hf1.continuous.continuousOn
  have hdc : ContinuousOn (deriv (deriv f)) (uIcc a b) :=
    (hf1.continuous_deriv_one).continuousOn
  have hAc : ContinuousOn (fun x => -(deriv (deriv f) x) / (deriv f x) ^ 2) (uIcc a b) :=
    hdc.neg.div (hfc.pow 2) (fun x hx => pow_ne_zero 2 (hne x hx))
  have hh := integral_expPhase_mul_deriv_mul
    (A := fun x => (deriv f x)⁻¹)
    (A' := fun x => -(deriv (deriv f) x) / (deriv f x) ^ 2)
    (fun x _ => (hf0 x).hasDerivAt)
    (fun x hx => ((hf1d x).hasDerivAt.inv (hne x hx))) hfc hAc
  convert hh using 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hne x hx), Complex.ofReal_one, mul_one]

end WaveTurbulence.VdCB
