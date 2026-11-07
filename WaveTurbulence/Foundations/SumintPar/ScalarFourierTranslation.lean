/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ScalarFourierScaling

/-!
# Translation leaves the scalar time-cutoff Fourier modulus unchanged

Only a unit Fourier character is introduced by moving a time-cell
center, so all weighted Fourier mass bounds are uniform in that center.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace WaveTurbulence.SumintPar

/-- Scalar translation changes no Fourier modulus in the source normalization. -/
theorem norm_scalarFourier_translate (f : ℝ → ℂ) (c ξ : ℝ) :
    ‖𝓕 (fun t => f (t+c)) ξ‖ = ‖𝓕 f ξ‖ := by
  have he := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ ℝ) f c) ξ
  have hn := congrArg norm he
  change ‖𝓕 (fun t => f (t+c)) ξ‖ = ‖Real.fourierChar ((innerₗ ℝ) c ξ) • 𝓕 f ξ‖ at hn
  simpa only [Circle.norm_smul] using hn

/-- Fourier moduli of translated scalar time dilations are uniform in the center. -/
theorem norm_scalarFourier_cell {h : ℝ} (hh : 0 < h) (f : ℝ → ℂ) (c ξ : ℝ) :
    ‖𝓕 (fun t => f ((t-c)/h)) ξ‖ = h*‖𝓕 f (h*ξ)‖ := by
  have ht := norm_scalarFourier_translate (fun t => f (t/h)) (-c) ξ
  simpa only [sub_eq_add_neg,norm_scalarFourier_div hh] using ht

end WaveTurbulence.SumintPar
