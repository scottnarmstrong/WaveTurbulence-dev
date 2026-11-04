/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! # Actual momentum modulation derivatives via the landed Fourier calculus

The source root phase is the Fourier transform of a Dirac mass. The
Mathlib finite derivative formula gives its exact polynomial frequency loss.
-/

public section
noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff

namespace WaveTurbulence.Incoh

/-- The actual root modulation is a Fourier transform of a Dirac mass. -/
theorem momentumModulation_eq_dirac_fourier {d : ℕ} (v : Mom d) :
    (fun k : Mom d => (Real.fourierChar (inner ℝ v k) : ℂ)) =
      VectorFourier.fourierIntegral Real.fourierChar (Measure.dirac (-v))
        (innerSL ℝ (E := Mom d)).toLinearMap₁₂ (fun _ => (1 : ℂ)) := by
  funext k
  simp [VectorFourier.fourierIntegral, Circle.smul_def]

/-- A fixed source root modulation is smooth at every momentum. -/
theorem contDiff_momentumModulation {d : ℕ} (v : Mom d) :
    ContDiff ℝ ∞ (fun k : Mom d => (Real.fourierChar (inner ℝ v k) : ℂ)) := by
  rw [momentumModulation_eq_dirac_fourier]
  exact VectorFourier.contDiff_fourierIntegral (innerSL ℝ) (N := ⊤)
    (fun n _ => integrable_dirac (by simp))

/-- Exact actual derivative formula, retaining the unit root phase. -/
theorem iteratedFDeriv_momentumModulation {d : ℕ} (v k : Mom d) (j : ℕ) :
    iteratedFDeriv ℝ j (fun k : Mom d => (Real.fourierChar (inner ℝ v k) : ℂ)) k =
      Real.fourierChar (inner ℝ v k) •
        VectorFourier.fourierPowSMulRight (innerSL ℝ) (fun _ : Mom d => (1 : ℂ)) (-v) j := by
  rw [momentumModulation_eq_dirac_fourier,
    VectorFourier.iteratedFDeriv_fourierIntegral (innerSL ℝ) (N := (j : ℕ∞))
      (fun n _ => integrable_dirac (by simp)) aestronglyMeasurable_const (le_refl _)]
  simp only [VectorFourier.fourierIntegral, integral_dirac]
  change Real.fourierChar (-(inner ℝ (-v) k)) • _ = _
  rw [inner_neg_left, neg_neg]

/-- Actual modulation derivatives vary continuously with their frequency parameter. -/
theorem continuous_iteratedFDeriv_momentumModulation_frequency {d : ℕ} (k : Mom d) (j : ℕ) :
    Continuous (fun v : Mom d =>
      iteratedFDeriv ℝ j (fun k : Mom d => (Real.fourierChar (inner ℝ v k) : ℂ)) k) := by
  simp_rw [iteratedFDeriv_momentumModulation]
  have hp : Continuous (fun v : Mom d =>
      VectorFourier.fourierPowSMulRight (innerSL ℝ) (fun _ : Mom d => (1 : ℂ)) (-v) j) :=
    (Continuous.fourierPowSMulRight (innerSL ℝ) continuous_const j).comp continuous_neg
  exact (Real.continuous_fourierChar.comp (by fun_prop)).smul hp

/-- The actual `j`-th operator derivative has the expected polynomial frequency bound. -/
theorem norm_iteratedFDeriv_momentumModulation_le {d : ℕ} (v k : Mom d) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun k : Mom d => (Real.fourierChar (inner ℝ v k) : ℂ)) k‖ ≤
      (2 * Real.pi) ^ j * ‖v‖ ^ j := by
  rw [momentumModulation_eq_dirac_fourier,
    VectorFourier.iteratedFDeriv_fourierIntegral (innerSL ℝ) (N := (j : ℕ∞))
      (fun n _ => integrable_dirac (by simp)) aestronglyMeasurable_const (le_refl _)]
  simp only [VectorFourier.fourierIntegral, integral_dirac, Circle.norm_smul]
  apply (VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) (fun _ : Mom d => (1 : ℂ)) (-v) j).trans
  simp only [norm_one, mul_one, norm_neg]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_of_le_one_right (by positivity) (norm_innerSL_le ℝ (E := Mom d))

end WaveTurbulence.Incoh
