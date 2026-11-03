/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.CubicAmplitude
public import Mathlib.Data.Fin.VecNotation

/-!
# Translation of the cubic phases

Spatial centers in TARGET `lemcubic0` only translate the linear frequency
and contribute a unit complex factor. No estimate depends on those centers.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory

/-- The linear phase produced by translating the quadratic form. -/
@[expose] def cubicFrequencyShift (kind : CubicPhase) (s t : ℝ) (a : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  match kind with
  | .cross => ![t * a 1 + s * a 2, t * a 0, s * a 0]
  | .collision => ![t * a 1 + s * a 2, t * a 0 + s * a 2,
      s * (a 0 + a 1 - 2 * a 2)]

/-- The exact polarization identity for the two source forms. -/
theorem scalarQuadratic_translate (kind : CubicPhase) (s t : ℝ) (a p : Fin 3 → ℝ) :
    scalarQuadratic kind s t (p + a) = scalarQuadratic kind s t p +
      scalarQuadratic kind s t a + ∑ i, cubicFrequencyShift kind s t a i * p i := by
  cases kind <;> simp [scalarQuadratic, cubicFrequencyShift, Fin.sum_univ_succ] <;> ring

/-- The scalar integral with arbitrary translated cutoff centers. -/
@[expose] noncomputable def translatedScalarCubicIntegral (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) (a ν : Fin 3 → ℝ) : ℂ :=
  ∫ p : Fin 3 → ℝ, cubicProduct f (p - a) *
    (Real.fourierChar ((∑ i, ν i * p i) + scalarQuadratic kind s t p) : ℂ)

/-- Exact translation formula, including its harmless constant phase. -/
theorem translatedScalarCubicIntegral_eq (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) (a ν : Fin 3 → ℝ) :
    translatedScalarCubicIntegral kind f s t a ν =
      (Real.fourierChar ((∑ i, ν i * a i) + scalarQuadratic kind s t a) : ℂ) *
        scalarCubicIntegral kind f s t (ν + cubicFrequencyShift kind s t a) := by
  unfold translatedScalarCubicIntegral
  rw [← integral_add_right_eq_self _ a]
  unfold scalarCubicIntegral scalarCubicAmplitude
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  dsimp only
  rw [add_sub_cancel_right, scalarQuadratic_translate]
  have he : (∑ i, ν i * (p + a) i) +
      (scalarQuadratic kind s t p + scalarQuadratic kind s t a +
        ∑ i, cubicFrequencyShift kind s t a i * p i) =
      ((∑ i, ν i * a i) + scalarQuadratic kind s t a) +
        (scalarQuadratic kind s t p + ∑ i, (ν + cubicFrequencyShift kind s t a) i * p i) := by
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    ring
  rw [he]
  simp only [AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/-- Uniformity in all spatial centers follows by translating frequencies. -/
theorem norm_translatedScalarCubicIntegral (kind : CubicPhase)
    (f : Fin 3 → ScalarCutoff) (s t : ℝ) (a ν : Fin 3 → ℝ) :
    ‖translatedScalarCubicIntegral kind f s t a ν‖ =
      ‖scalarCubicIntegral kind f s t (ν + cubicFrequencyShift kind s t a)‖ := by
  rw [translatedScalarCubicIntegral_eq, norm_mul, Circle.norm_coe, one_mul]

end WaveTurbulence.LemLin
