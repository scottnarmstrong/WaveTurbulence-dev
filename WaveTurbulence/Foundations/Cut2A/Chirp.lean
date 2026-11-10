/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Fourier.FourierL1Sobolev
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
/-! Local jet bounds for a compactly supported chirp; C2-A, NOTES §3.1. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ContDiff FourierTransform
namespace WaveTurbulence.Cut2A
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A scalar character is the Fourier transform of a scalar Dirac mass. -/
theorem character_eq_dirac : (fun s : ℝ => (Real.fourierChar s : ℂ)) =
    VectorFourier.fourierIntegral Real.fourierChar (Measure.dirac (-1 : ℝ))
      (innerSL ℝ (E := ℝ)).toLinearMap₁₂ (fun _ => (1 : ℂ)) := by
  funext s
  simp [VectorFourier.fourierIntegral, Circle.smul_def]

theorem character_smooth : ContDiff ℝ ∞ (fun s : ℝ => (Real.fourierChar s : ℂ)) := by
  rw [character_eq_dirac]
  exact VectorFourier.contDiff_fourierIntegral (innerSL ℝ) (N := ⊤)
    (fun n _ => integrable_dirac (by simp))

end WaveTurbulence.Cut2A
