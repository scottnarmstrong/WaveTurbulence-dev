/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.EndpointKernelConvolution

/-!
# Nonnegative scalar power kernels and their moments

This notation keeps the endpoint Tonelli and Young arguments in the
nonnegative extended reals, while evaluating every finite kernel moment
as the ordinary integral of its explicit scalar power.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- The nonnegative scalar inverse-bracket kernel of real order `p`. -/
@[expose] noncomputable def scalarPowerKernel (p t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (scalarBracket t^(-p))

/-- Every scalar kernel is measurable. -/
theorem measurable_scalarPowerKernel (p : ℝ) : Measurable (scalarPowerKernel p) := by
  apply ENNReal.measurable_ofReal.comp
  have hc : Continuous scalarBracket := by unfold scalarBracket; fun_prop
  exact (hc.rpow_const (fun t => Or.inl (zero_lt_one.trans_le (one_le_scalarBracket t)).ne')).measurable

/-- Powers multiply the kernel order exactly. -/
theorem scalarPowerKernel_rpow (p t : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    scalarPowerKernel p t^q = scalarPowerKernel (p*q) t := by
  unfold scalarPowerKernel
  rw [ENNReal.ofReal_rpow_of_nonneg
    (Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket t)) _) hq,
    ← Real.rpow_mul (zero_le_one.trans (one_le_scalarBracket t))]
  congr 2
  ring

/-- All moments with combined power greater than one are finite and explicit. -/
theorem lintegral_scalarPowerKernel_rpow (p : ℝ) {q : ℝ} (hq : 0 ≤ q) (hpq : 1 < p*q) :
    (∫⁻ t : ℝ, scalarPowerKernel p t^q) =
      ENNReal.ofReal (∫ t : ℝ, scalarBracket t^(-(p*q))) := by
  simp_rw [scalarPowerKernel_rpow p _ hq]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_scalarBracket_rpow hpq)
    (ae_of_all _ (fun _ => Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _))).symm

/-- The kernel of order one has the literal endpoint denominator. -/
theorem scalarPowerKernel_one (t : ℝ) : scalarPowerKernel 1 t = ENNReal.ofReal (1/scalarBracket t) := by
  simp only [scalarPowerKernel, Real.rpow_neg_one, one_div]

/-- Reflection leaves the scalar kernel unchanged. -/
theorem scalarPowerKernel_neg (p t : ℝ) : scalarPowerKernel p (-t) = scalarPowerKernel p t := by
  simp only [scalarPowerKernel, scalarBracket, neg_sq]

end WaveTurbulence.SumintPar
