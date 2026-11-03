/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeInterpolation
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# Coordinate and Euclidean Fourier transforms

Transport between product-coordinate time variables and Mathlib's
inner-product-space Fourier transform. Both use the same Lebesgue measure.
-/

public section

open MeasureTheory WithLp
open scoped FourierTransform

namespace WaveTurbulence.Fourier

/-- Changing the norm on the finite coordinate space does not change the
Fourier integral or its normalization. -/
theorem timeFourier_eq_euclidean {r : ℕ} (f : (Fin r → ℝ) → ℂ) (ξ : Fin r → ℝ) :
    timeFourier f ξ = 𝓕 (fun x : EuclideanSpace ℝ (Fin r) => f (ofLp x)) (toLp 2 ξ) := by
  have hh := (PiLp.volume_preserving_ofLp (Fin r)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin r → ℝ)).symm.measurableEmbedding
    (fun t => Real.fourierChar (-timePairing r t ξ) • f t)
  change (∫ t, Real.fourierChar (-timePairing r t ξ) • f t) = _
  rw [← hh]
  change (∫ t : EuclideanSpace ℝ (Fin r),
    Real.fourierChar (-timePairing r (ofLp t) ξ) • f (ofLp t)) = _
  rw [Real.fourier_eq]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    simp [timePairing, PiLp.inner_apply, dotProduct, mul_comm]

/-- Coordinate form of Fourier inversion at continuity points. -/
theorem timeFourier_inversion {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hhf : Integrable (timeFourier f)) (hc : Continuous f)
    (t : Fin r → ℝ) : timeFourier (timeFourier f) (-t) = f t := by
  have hfi := (PiLp.volume_preserving_ofLp (Fin r)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin r → ℝ)).symm.measurableEmbedding (g := f) |>.mpr hf
  have he : (fun x : EuclideanSpace ℝ (Fin r) => timeFourier f (ofLp x)) =
      𝓕 (fun x : EuclideanSpace ℝ (Fin r) => f (ofLp x)) := by
    funext x
    simpa only [toLp_ofLp] using timeFourier_eq_euclidean f (ofLp x)
  have hhi := (PiLp.volume_preserving_ofLp (Fin r)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin r → ℝ)).symm.measurableEmbedding
      (g := timeFourier f) |>.mpr hhf
  simp only [Function.comp_def] at hhi
  rw [he] at hhi
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin r) => f (ofLp x)) :=
    hc.comp (PiLp.continuous_ofLp 2 _)
  have hinv := hcont.fourierInv_fourier_eq hfi hhi
  rw [timeFourier_eq_euclidean, he]
  have hpoint := congrFun hinv (toLp 2 t)
  rw [Real.fourierInv_eq_fourier_neg] at hpoint
  simpa using hpoint

end WaveTurbulence.Fourier
