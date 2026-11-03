/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.ScalarStationary

/-!
# Frequency recurrences for the cubic integral

Integration by parts expresses multiplication by a frequency coordinate in
terms of one differentiated scalar cutoff and three coordinate-weighted
cutoffs. All remain in the fixed compact amplitude class.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Finset
open scoped Classical

/-- The positive Fourier convention for an arbitrary amplitude. -/
theorem timeFourier_neg_eq_integral {n : ℕ} (f : (Fin n → ℝ) → ℂ) (ν : Fin n → ℝ) :
    Fourier.timeFourier f (-ν) =
      ∫ p, f p * (Real.fourierChar (∑ i, ν i * p i) : ℂ) := by
  unfold Fourier.timeFourier VectorFourier.fourierIntegral
  apply integral_congr_ae
  apply ae_of_all
  intro p
  have he : -(Fourier.timePairing n p (-ν)) = ∑ i, ν i * p i := by
    change -(∑ i, p i * -ν i) = ∑ i, ν i * p i
    simp only [mul_neg, Finset.sum_neg_distrib, neg_neg]
    exact sum_congr rfl (fun _ _ => mul_comm _ _)
  simp only [Circle.smul_def, smul_eq_mul]
  change (Real.fourierChar (-(Fourier.timePairing n p (-ν))) : ℂ) * f p =
    f p * (Real.fourierChar (∑ i, ν i * p i) : ℂ)
  rw [he, mul_comm]

/-- Expand the positive Fourier integral of the differentiated amplitude. -/
theorem integral_partialDeriv_cubic (kind : CubicPhase) (f : Fin 3 → ScalarCutoff)
    (s t : ℝ) (j : Fin 3) (ν : Fin 3 → ℝ) :
    (∫ p, partialDeriv j (scalarCubicAmplitude kind f s t) p *
      (Real.fourierChar (∑ i, ν i * p i) : ℂ)) =
      scalarCubicIntegral kind (Function.update f j (f j).differentiate) s t ν +
        (2 * Real.pi * Complex.I) * ∑ k, (cubicMatrix kind s t j k : ℂ) *
          scalarCubicIntegral kind (Function.update f k (f k).mulCoordinate) s t ν := by
  let χ : (Fin 3 → ℝ) → ℂ := fun p => (Real.fourierChar (∑ i, ν i * p i) : ℂ)
  let D : (Fin 3 → ℝ) → ℂ := fun p =>
    scalarCubicAmplitude kind (Function.update f j (f j).differentiate) s t p * χ p
  let M : Fin 3 → (Fin 3 → ℝ) → ℂ := fun k p =>
    (cubicMatrix kind s t j k : ℂ) *
      (scalarCubicAmplitude kind (Function.update f k (f k).mulCoordinate) s t p * χ p)
  have hD : Integrable D := scalarCubic_integrand_integrable kind _ s t ν
  have hM (k : Fin 3) : Integrable (M k) :=
    (scalarCubic_integrand_integrable kind _ s t ν).const_mul _
  have he : (fun p => partialDeriv j (scalarCubicAmplitude kind f s t) p * χ p) =
      fun p => D p + (2 * Real.pi * Complex.I) * ∑ k, M k p := by
    funext p
    dsimp only [D, M]
    calc
      _ = (scalarCubicAmplitude kind (Function.update f j (f j).differentiate) s t p +
          (2 * Real.pi * Complex.I) * ((cubicFrequencyShift kind s t p j : ℂ) *
            scalarCubicAmplitude kind f s t p)) * χ p := by
        rw [partialDeriv_scalarCubicAmplitude]
        ring
      _ = _ := by
        rw [cubicGradient_mul_amplitude, add_mul, mul_assoc, Finset.sum_mul]
        simp only [mul_assoc]
  change (∫ p, partialDeriv j (scalarCubicAmplitude kind f s t) p * χ p) = _
  rw [he, integral_add hD ((integrable_finsetSum _ (fun k _ => hM k)).const_mul _),
    integral_const_mul, integral_finsetSum _ (fun k _ => hM k)]
  congr 2
  apply sum_congr rfl
  intro k _
  exact integral_const_mul _ _

/-- The exact coordinate frequency recurrence, in the source's positive convention. -/
theorem scalarCubic_frequency_identity (kind : CubicPhase) (f : Fin 3 → ScalarCutoff)
    (s t : ℝ) (j : Fin 3) (ν : Fin 3 → ℝ) :
    -(2 * Real.pi * Complex.I * (ν j : ℂ)) * scalarCubicIntegral kind f s t ν =
      scalarCubicIntegral kind (Function.update f j (f j).differentiate) s t ν +
        (2 * Real.pi * Complex.I) * ∑ k, (cubicMatrix kind s t j k : ℂ) *
          scalarCubicIntegral kind (Function.update f k (f k).mulCoordinate) s t ν := by
  have he := timeFourier_partialDeriv (scalarCubicAmplitude_contDiff kind f s t)
    (scalarCubicAmplitude_hasCompactSupport kind f s t) j (-ν)
  rw [timeFourier_neg_eq_integral, integral_partialDeriv_cubic,
    ← scalarCubicIntegral_eq_timeFourier] at he
  simpa only [Pi.neg_apply, Complex.ofReal_neg, mul_neg] using he.symm

end WaveTurbulence.LemLin
