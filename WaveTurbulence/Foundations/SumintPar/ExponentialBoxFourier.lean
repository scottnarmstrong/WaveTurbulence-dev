/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ExponentialEndpointBounds
public import WaveTurbulence.Foundations.Fourier.CoordinateProducts
import Mathlib.Tactic

/-!
# Fourier transform of the explicit rectangular extension kernel

For every fixed input-time vector the shifted output-time domain
factorizes into one finite interval and two negative half-lines.
The exponential weights give an exact product of endpoint integrals.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set
open scoped FourierTransform

namespace WaveTurbulence.SumintPar

/-- Scalar exponential on a specified interval or half-line. -/
@[expose] noncomputable def exponentialInterval (S : Set ℝ) (σ : ℝ) : ℝ → ℂ :=
  S.indicator (fun t => (Real.exp (σ*t) : ℂ))

/-- The rectangular output-time kernel used by the explicit local extension. -/
@[expose] noncomputable def exponentialBox (a b u : ℝ) (t : Fin 3 → ℝ) : ℂ :=
  ∏ j, (![exponentialInterval (Icc a b) (-1), exponentialInterval (Iio u) 1,
    exponentialInterval (Iio u) 1] j) (t j)

/-- Fourier transforming the scalar exponential indicator gives its literal interval integral. -/
theorem fourier_exponentialInterval (S : Set ℝ) (hS : MeasurableSet S) (σ ξ : ℝ) :
    𝓕 (exponentialInterval S σ) ξ =
      ∫ t in S, (Real.exp (σ*t) : ℂ) * (Real.fourierChar (-ξ*t) : ℂ) := by
  rw [Real.fourier_eq, ← integral_indicator hS]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  by_cases ht : t ∈ S
  · simp [exponentialInterval, ht, Circle.smul_def, mul_comm]
  · simp [exponentialInterval, ht, Circle.smul_def]

/-- Exact product formula for the Fourier transform of the source rectangular domain. -/
theorem timeFourier_exponentialBox (a b u : ℝ) (ξ : Fin 3 → ℝ) :
    Fourier.timeFourier (exponentialBox a b u) ξ =
      (∫ t in Icc a b, (Real.exp (-t) : ℂ) * (Real.fourierChar (-ξ 0*t) : ℂ)) *
      (∫ t in Iio u, (Real.exp t : ℂ) * (Real.fourierChar (-ξ 1*t) : ℂ)) *
      (∫ t in Iio u, (Real.exp t : ℂ) * (Real.fourierChar (-ξ 2*t) : ℂ)) := by
  unfold exponentialBox
  rw [Fourier.timeFourier_coordinate_product, Fin.prod_univ_three]
  change 𝓕 (exponentialInterval (Icc a b) (-1)) (ξ 0) *
    𝓕 (exponentialInterval (Iio u) 1) (ξ 1) *
    𝓕 (exponentialInterval (Iio u) 1) (ξ 2) = _
  have h₀ : 𝓕 (exponentialInterval (Icc a b) (-1)) (ξ 0) =
      ∫ t in Icc a b, (Real.exp (-t) : ℂ) * (Real.fourierChar (-ξ 0*t) : ℂ) := by
    simpa only [neg_one_mul] using fourier_exponentialInterval (Icc a b) measurableSet_Icc (-1) (ξ 0)
  have h₁ : 𝓕 (exponentialInterval (Iio u) 1) (ξ 1) =
      ∫ t in Iio u, (Real.exp t : ℂ) * (Real.fourierChar (-ξ 1*t) : ℂ) := by
    simpa only [one_mul] using fourier_exponentialInterval (Iio u) measurableSet_Iio 1 (ξ 1)
  have h₂ : 𝓕 (exponentialInterval (Iio u) 1) (ξ 2) =
      ∫ t in Iio u, (Real.exp t : ℂ) * (Real.fourierChar (-ξ 2*t) : ℂ) := by
    simpa only [one_mul] using fourier_exponentialInterval (Iio u) measurableSet_Iio 1 (ξ 2)
  exact congrArg₂ (fun x y : ℂ => x*y) (congrArg₂ (fun x y : ℂ => x*y) h₀ h₁) h₂

/-- Uniform product-bracket bound for all actual endpoint configurations. -/
theorem norm_timeFourier_exponentialBox_le {a b u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : u ≤ 0) (ξ : Fin 3 → ℝ) :
    ‖Fourier.timeFourier (exponentialBox a b u) ξ‖ ≤
      2 * ∏ j, (1 / scalarBracket (ξ j)) := by
  rw [timeFourier_exponentialBox, norm_mul, norm_mul]
  have hb₀ : 0 < scalarBracket (ξ 0) := zero_lt_one.trans_le (one_le_scalarBracket _)
  have hb₁ : 0 < scalarBracket (ξ 1) := zero_lt_one.trans_le (one_le_scalarBracket _)
  have hb₂ : 0 < scalarBracket (ξ 2) := zero_lt_one.trans_le (one_le_scalarBracket _)
  have h₀ := norm_integral_exp_neg_char_Icc_le ha hab (ξ 0)
  have h₁ := norm_integral_exp_pos_char_Iio_le hu (ξ 1)
  have h₂ := norm_integral_exp_pos_char_Iio_le hu (ξ 2)
  calc
    _ ≤ (2 / scalarBracket (ξ 0)) * (1 / scalarBracket (ξ 1)) * (1 / scalarBracket (ξ 2)) :=
      mul_le_mul (mul_le_mul h₀ h₁ (norm_nonneg _) (by positivity)) h₂
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [Fin.prod_univ_three]; ring

end WaveTurbulence.SumintPar
