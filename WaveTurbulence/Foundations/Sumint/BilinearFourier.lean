/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PairPhaseCoordinates
import Mathlib.Tactic

/-!
# Fourier transform of the compact bilinear amplitude

The negative Fourier character shifts the two arbitrary linear
frequencies. All integrals use the same product Lebesgue normalization.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Sumint

/-- The coordinate Fourier transform is the physical bilinear integral with shifted frequencies. -/
theorem timeFourier_flatBilinearAmplitude {d : ℕ} (c : Fin 2 → Fin d → ℝ)
    (s : ℝ) (ξ ζ : Mom d) (ν : Fin (2*d) → ℝ) :
    Fourier.timeFourier (flatBilinearAmplitude c s ξ ζ) ν =
      ∫ p : Mom d × Mom d, flatBilinearAmplitude c s
        (ξ - flatMomentum 0 ν) (ζ - flatMomentum 1 ν) (pairFlatten d p) := by
  have hh := (pairFlatten_measurePreserving d).integral_comp
    (pairFlatten d).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun z => Real.fourierChar (-Fourier.timePairing (2*d) z ν) • flatBilinearAmplitude c s ξ ζ z)
  change (∫ z, Real.fourierChar (-Fourier.timePairing (2*d) z ν) •
    flatBilinearAmplitude c s ξ ζ z) = _
  rw [← hh]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  simp only [Circle.smul_def, smul_eq_mul, flatBilinearAmplitude,
    pair_timePairing_eq, flatMomentum_pairFlatten_zero, flatMomentum_pairFlatten_one,
    inner_sub_right, Real.fourierChar_apply]
  rw [mul_left_comm]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end WaveTurbulence.Sumint
