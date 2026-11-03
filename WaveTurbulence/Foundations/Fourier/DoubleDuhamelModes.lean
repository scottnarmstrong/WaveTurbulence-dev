/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeIntegralOperators
public import WaveTurbulence.Foundations.Fourier.CoordinateProducts
import Mathlib.Tactic

/-!
# The tensor Duhamel kernel on Fourier modes

The literal two-time operator acts on an input Fourier mode as the
product of its one-dimensional modes. Its output Fourier transform is
exactly the tensor kernel whose four-bracket bound was proved earlier.
-/

public section

namespace WaveTurbulence.Fourier

/-- A two-time cutoff Duhamel output mode. -/
@[expose] noncomputable def doubleDuhamelMode (χ : ℝ → ℝ) (σ t : Fin 2 → ℝ) : ℂ :=
  duhamelMode χ (σ 0) (t 0) * duhamelMode χ (σ 1) (t 1)

/-- The tensor kernel is the actual output Fourier transform of the tensor mode. -/
theorem timeFourier_doubleDuhamelMode (χ : ℝ → ℝ) (ξ σ : Fin 2 → ℝ) :
    timeFourier (doubleDuhamelMode χ σ) ξ = doubleDuhamelKernel χ ξ σ := by
  have he : doubleDuhamelMode χ σ = fun t => ∏ j : Fin 2, duhamelMode χ (σ j) (t j) := by
    funext t
    simp [doubleDuhamelMode, Fin.prod_univ_two]
  rw [he, timeFourier_coordinate_product]
  simp [Fin.prod_univ_two, doubleDuhamelKernel, duhamelKernel]

/-- Literal action of the two-time operator on a product of input Fourier characters. -/
theorem cutoffDoubleIntegral_mode (χ : ℝ → ℝ) (σ t : Fin 2 → ℝ) :
    cutoffDoubleIntegral χ (fun u =>
      (Real.fourierChar (σ 0 * u 0) : ℂ) * (Real.fourierChar (σ 1 * u 1) : ℂ)) t =
      doubleDuhamelMode χ σ t := by
  unfold cutoffDoubleIntegral doubleDuhamelMode duhamelMode duhamelPrimitive
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have he (u v : ℝ) : (χ u : ℂ) * (χ v : ℂ) *
      ((Real.fourierChar (σ 0 * u) : ℂ) * (Real.fourierChar (σ 1 * v) : ℂ)) =
      ((χ u : ℂ) * (Real.fourierChar (σ 0 * u) : ℂ)) *
        ((χ v : ℂ) * (Real.fourierChar (σ 1 * v) : ℂ)) := by ring
  simp_rw [he, intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  ring

end WaveTurbulence.Fourier
