/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ScalarFourierMass
public import WaveTurbulence.Foundations.SumintPar.ScalarMeasureScaling

/-!
# Uniform scalar Fourier mass of a translated time-cell cutoff

For 0<h<=1 the bracket-weighted Fourier mass costs at most h inverse.
The translation center does not enter the estimate. This supplies an
explicit polynomial scale loss for the actual smooth partition.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ENNReal
open scoped FourierTransform
namespace WaveTurbulence.SumintPar

/-- A positive small scale moves the scalar Japanese bracket in the correct direction. -/
theorem mul_scalarBracket_le_scaled {h : ℝ} (hh : h ∈ Set.Ioc (0:ℝ) 1) (ξ : ℝ) :
    h*scalarBracket ξ ≤ scalarBracket (h*ξ) := by
  change h*Real.sqrt (1+ξ^2) ≤ Real.sqrt (1+(h*ξ)^2)
  have he : h*Real.sqrt (1+ξ^2) = Real.sqrt (h^2*(1+ξ^2)) := by
    rw [Real.sqrt_mul (sq_nonneg h),Real.sqrt_sq_eq_abs,abs_of_pos hh.1]
  rw [he]
  apply Real.sqrt_le_sqrt
  nlinarith only [hh.1,hh.2]

/-- The scalar bracket-weighted Fourier mass of any translated h-cell costs at most h inverse. -/
theorem scalarFourierMass_cell_le {h : ℝ} (hh : h ∈ Set.Ioc (0:ℝ) 1) (f : ℝ → ℂ) (c : ℝ) :
    scalarFourierMass (fun t => f ((t-c)/h)) ≤ ENNReal.ofReal h⁻¹*scalarFourierMass f := by
  calc
    _ ≤ ∫⁻ ξ : ℝ, ENNReal.ofReal (scalarBracket (h*ξ))*‖𝓕 f (h*ξ)‖ₑ := by
      apply lintegral_mono
      intro ξ
      change ENNReal.ofReal (scalarBracket ξ)*‖𝓕 (fun t => f ((t-c)/h)) ξ‖ₑ ≤ _
      rw [← ofReal_norm,norm_scalarFourier_cell hh.1,ENNReal.ofReal_mul hh.1.le,ofReal_norm,← mul_assoc]
      apply mul_le_mul' _ le_rfl
      rw [← ENNReal.ofReal_mul (zero_le_one.trans (one_le_scalarBracket _))]
      exact ENNReal.ofReal_le_ofReal (by simpa only [mul_comm] using mul_scalarBracket_le_scaled hh ξ)
    _ = _ := lintegral_scalar_mul hh.1 (fun ξ => ENNReal.ofReal (scalarBracket ξ)*‖𝓕 f ξ‖ₑ)

end WaveTurbulence.SumintPar
