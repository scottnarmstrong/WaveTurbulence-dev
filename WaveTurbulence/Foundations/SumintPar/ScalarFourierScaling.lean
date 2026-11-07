/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CoordinateProducts
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Exact scalar Fourier dilation for time-cell multipliers

The scale is a positive real h. The transform of f(t/h) is h times the
transform of f at h times the frequency, with the source 2 pi convention.
No integrability hypothesis is needed for this change-of-variables identity.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform
namespace WaveTurbulence.SumintPar

/-- The scalar Fourier transform in the same real coordinate phase used by the source. -/
theorem scalarFourier_eq (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ t : ℝ, (Real.fourierChar (-(t*ξ)):ℂ)*f t := by
  rw [Real.fourier_eq]
  simp only [Circle.smul_def,smul_eq_mul,RCLike.inner_apply',conj_trivial,mul_comm]

/-- Positive scalar time dilation has its exact native Fourier transform. -/
theorem scalarFourier_div {h : ℝ} (hh : 0 < h) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun t => f (t/h)) ξ = (h:ℂ)*𝓕 f (h*ξ) := by
  let g (t : ℝ) := (Real.fourierChar (-(t*(h*ξ))):ℂ)*f t
  rw [scalarFourier_eq]
  calc
    _ = ∫ t : ℝ, g (h⁻¹*t) := by
      apply integral_congr_ae
      apply ae_of_all
      intro t
      have ha : (h⁻¹*t)*(h*ξ) = t*ξ := by field_simp
      dsimp [g]
      rw [ha,div_eq_mul_inv,mul_comm t h⁻¹]
    _ = |h| • ∫ t : ℝ, g t := Measure.integral_comp_inv_mul_left g h
    _ = _ := by
      rw [abs_of_pos hh,scalarFourier_eq]
      rfl

/-- Scalar dilation multiplies the Fourier modulus by the positive time scale. -/
theorem norm_scalarFourier_div {h : ℝ} (hh : 0 < h) (f : ℝ → ℂ) (ξ : ℝ) :
    ‖𝓕 (fun t => f (t/h)) ξ‖ = h*‖𝓕 f (h*ξ)‖ := by
  rw [scalarFourier_div hh,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]

end WaveTurbulence.SumintPar
