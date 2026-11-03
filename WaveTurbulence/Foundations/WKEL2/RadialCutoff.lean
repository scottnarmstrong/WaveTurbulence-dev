/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.PolarRadial

/-!
# Normalization of the radial cutoff defining angular measure
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- The mass of the positive radial interval `(0,1)`. -/
@[expose] def radialUnitMass (n : ℕ) : ℝ≥0∞ :=
  Measure.volumeIoiPow n (Iio (⟨1, zero_lt_one⟩ : Ioi (0 : ℝ)))

/-- Explicit normalization of the radial interval. -/
theorem radialUnitMass_eq (n : ℕ) :
    radialUnitMass n = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  rw [radialUnitMass, Measure.volumeIoiPow_apply_Iio]
  simp only [one_pow]

/-- Integrating a constant over the radial cutoff, including infinite constants. -/
theorem lintegral_radius_lt_one (n : ℕ) (c : ℝ≥0∞) :
    (∫⁻ r : Ioi (0 : ℝ), if r.1 < 1 then c else 0 ∂Measure.volumeIoiPow n) =
      radialUnitMass n * c := by
  have h := lintegral_indicator (μ := Measure.volumeIoiPow n)
    (s := Iio (⟨1, zero_lt_one⟩ : Ioi (0 : ℝ))) measurableSet_Iio (fun _ => c)
  simp only [Set.indicator, mem_Iio, lintegral_const, Measure.restrict_apply_univ] at h
  change (∫⁻ r : Ioi (0 : ℝ), if r.1 < 1 then c else 0 ∂Measure.volumeIoiPow n) =
    c * radialUnitMass n at h
  exact h.trans (mul_comm _ _)

/-- The two independent radial cutoffs each contribute `1/(n+1)`. -/
theorem lintegral_two_radial_cutoffs {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (n : ℕ) {J : α → ℝ≥0∞} (hJ : Measurable J) :
    (∫⁻ ρ : Ioi (0 : ℝ), ∫⁻ θ, ∫⁻ r : Ioi (0 : ℝ),
      (if ρ.1 < 1 ∧ r.1 < 1 then J θ else 0) ∂Measure.volumeIoiPow n ∂μ
        ∂Measure.volumeIoiPow n) =
      (radialUnitMass n) ^ 2 * ∫⁻ θ, J θ ∂μ := by
  have hinner (ρ : Ioi (0 : ℝ)) :
      (∫⁻ θ, ∫⁻ r : Ioi (0 : ℝ), (if ρ.1 < 1 ∧ r.1 < 1 then J θ else 0)
        ∂Measure.volumeIoiPow n ∂μ) =
        if ρ.1 < 1 then radialUnitMass n * ∫⁻ θ, J θ ∂μ else 0 := by
    by_cases hρ : ρ.1 < 1
    · simp only [hρ, true_and, ↓reduceIte, lintegral_radius_lt_one]
      exact lintegral_const_mul _ hJ
    · simp only [hρ, false_and, ↓reduceIte, lintegral_zero]
  simp_rw [hinner]
  rw [lintegral_radius_lt_one, pow_two, mul_assoc]

end WaveTurbulence.WKEL2
