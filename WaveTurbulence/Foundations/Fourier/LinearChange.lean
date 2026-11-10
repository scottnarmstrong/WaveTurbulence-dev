/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeFourier
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-!
# Volume-preserving linear changes in Fourier-L¹ norms

TARGET L1007–L1012 uses unimodular integer changes of variables. The results
here hold for every real matrix with determinant of absolute value one.
The zero time-weight exponent is exactly the Fourier-L¹ norm.
-/

public section

open MeasureTheory Matrix
open scoped ENNReal

namespace WaveTurbulence.Fourier

private theorem det_ne_zero_of_abs_eq_one {r : ℕ} {A : Matrix (Fin r) (Fin r) ℝ}
    (hA : |A.det| = 1) : A.det ≠ 0 := by
  intro h
  simp [h] at hA

private theorem matrix_measurePreserving {r : ℕ} {A : Matrix (Fin r) (Fin r) ℝ}
    (hA : |A.det| = 1) : MeasurePreserving (Matrix.toLin' A) := by
  refine ⟨(Matrix.toLin' A).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (det_ne_zero_of_abs_eq_one hA)]
  simp only [abs_inv, hA, inv_one, ENNReal.ofReal_one, one_smul]

private theorem matrix_measurableEmbedding {r : ℕ} {A : Matrix (Fin r) (Fin r) ℝ}
    (hA : |A.det| = 1) : MeasurableEmbedding (Matrix.toLin' A) := by
  let e := A.toLinearEquiv' (A.invertibleOfIsUnitDet
    (isUnit_iff_ne_zero.mpr (det_ne_zero_of_abs_eq_one hA)))
  exact e.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

/-- Fourier covariance under a volume-preserving change of variables,
parametrized by the transpose frequency map. -/
theorem timeFourier_comp_matrix {r : ℕ} {A : Matrix (Fin r) (Fin r) ℝ}
    (hA : |A.det| = 1) (f : (Fin r → ℝ) → ℂ) (ξ : Fin r → ℝ) :
    timeFourier (fun t => f (A *ᵥ t)) (Aᵀ *ᵥ ξ) = timeFourier f ξ := by
  have hp := matrix_measurePreserving hA
  have he := matrix_measurableEmbedding hA
  have hi := hp.integral_comp he (fun t =>
    Real.fourierChar (-timePairing r t ξ) • f t)
  simp only [Matrix.toLin'_apply] at hi
  change (∫ t, Real.fourierChar (-timePairing r t (Aᵀ *ᵥ ξ)) • f (A *ᵥ t)) = _
  change (∫ t, Real.fourierChar (-timePairing r t (Aᵀ *ᵥ ξ)) • f (A *ᵥ t)) =
    ∫ t, Real.fourierChar (-timePairing r t ξ) • f t
  rw [← hi]
  have hpair (t : Fin r → ℝ) : timePairing r t (Aᵀ *ᵥ ξ) =
      timePairing r (A *ᵥ t) ξ := by
    change t ⬝ᵥ (Aᵀ *ᵥ ξ) = (A *ᵥ t) ⬝ᵥ ξ
    rw [dotProduct_mulVec, vecMul_transpose]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    change Real.fourierChar (-timePairing r t (Aᵀ *ᵥ ξ)) • f (A *ᵥ t) =
      Real.fourierChar (-timePairing r (A *ᵥ t) ξ) • f (A *ᵥ t)
    rw [hpair]

end WaveTurbulence.Fourier
