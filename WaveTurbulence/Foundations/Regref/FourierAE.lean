/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.TimeProduct
public import WaveTurbulence.Foundations.Fourier.TimeEuclidean
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Fourier inversion almost everywhere, and at continuity points, for the time Fourier transform

* `fourierInv_fourier_ae_eq_integrable`: `𝓕⁻ 𝓕 f = f` a.e. for `f, 𝓕 f ∈ L¹` on Euclidean space (tested against
  smooth compactly supported functions, `ae_eq_of_integral_contDiff_smul_eq`);
* `timeFourier_inversion_ae`, `timeFourier_continuous_representative`: the coordinate-time version, and the
  continuous representative `t ↦ (𝓕𝓕 f)(-t)` of a slice of finite `𝔛^θ` norm (`θ ≥ 0`);
* `timeFourier_inversion_at`, `enorm_le_timeFourierNorm_at`: inversion at a continuity point, and the pointwise
  bound `|f(t)| ≤ ‖f‖_{𝔛^θ}` there.

The proofs are those of the lg-spine scratch modules `EuclideanFourierAE`, `TimeFourierAE`, `TimePointwise`
(`/home/scott/wt-scratch/lg-spine`, sha256 `26038b49…`, `601fc5a2…`, `ff37f2f9…`), moved here unchanged except for
the namespace. Used by the trace estimates `Foundations/Regref/Trace00`, `Foundations/Regref/TraceDeriv`.
-/

public section

open MeasureTheory WithLp WaveTurbulence.Fourier
open scoped FourierTransform ContDiff ENNReal Topology

namespace WaveTurbulence.Regref

section Euclidean

variable {r : ℕ}

/-- Self-adjointness with two integrable inputs, one of which need not be smooth. -/
theorem integral_fourier_mul_eq_integrable {f g : EuclideanSpace ℝ (Fin r) → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ, 𝓕 f ξ * g ξ) = ∫ x, f x * 𝓕 g x := by
  simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, innerₗ_apply_apply, smul_eq_mul, LinearMap.flip_apply, real_inner_comm] using
    (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ (EuclideanSpace ℝ (Fin r)))
      Real.continuous_fourierChar continuous_inner hf hg)

/-- The inverse transform has the same self-adjointness identity. -/
theorem integral_fourierInv_mul_eq_integrable {f g : EuclideanSpace ℝ (Fin r) → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ, 𝓕⁻ f ξ * g ξ) = ∫ x, f x * 𝓕⁻ g x := by
  simpa only [Real.fourierInv_eq, VectorFourier.fourierIntegral, LinearMap.neg_apply,
    LinearMap.flip_apply, innerₗ_apply_apply, real_inner_comm, neg_neg, smul_eq_mul] using
    (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -(innerₗ (EuclideanSpace ℝ (Fin r))))
      Real.continuous_fourierChar continuous_inner.neg hf hg)

/-- Inverse transforms of L1 inputs are continuous, including at every comparison time. -/
theorem continuous_fourierInv_integrable {f : EuclideanSpace ℝ (Fin r) → ℂ} (hf : Integrable f) :
    Continuous (𝓕⁻ f) := by
  have he : 𝓕⁻ f = VectorFourier.fourierIntegral Real.fourierChar volume
      (-(innerₗ (EuclideanSpace ℝ (Fin r)))) f := by
    funext x
    simp only [Real.fourierInv_eq, VectorFourier.fourierIntegral, LinearMap.neg_apply,
      innerₗ_apply_apply, neg_neg]
  rw [he]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner.neg hf

/-- L1 Fourier inversion almost everywhere. The source Fourier norm uses functions rather
than equivalence classes; this theorem records exactly the representative ambiguity. -/
theorem fourierInv_fourier_ae_eq_integrable {f : EuclideanSpace ℝ (Fin r) → ℂ}
    (hf : Integrable f) (hhat : Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) =ᵐ[volume] f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (continuous_fourierInv_integrable hhat).locallyIntegrable hf.locallyIntegrable
  intro u hu hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ u) := hc.comp_left rfl
  have hu' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ u) := by fun_prop
  let U : SchwartzMap (EuclideanSpace ℝ (Fin r)) ℂ := hc'.toSchwartzMap hu'
  have h1 := integral_fourierInv_mul_eq_integrable hhat U.integrable
  rw [← SchwartzMap.fourierInv_coe] at h1
  have h2 := integral_fourier_mul_eq_integrable hf (𝓕⁻ U).integrable
  have he : 𝓕 (((𝓕⁻ U : SchwartzMap (EuclideanSpace ℝ (Fin r)) ℂ)) :
      EuclideanSpace ℝ (Fin r) → ℂ) = (U : EuclideanSpace ℝ (Fin r) → ℂ) := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  rw [he] at h2
  have hpair : (∫ x, U x * 𝓕⁻ (𝓕 f) x) = ∫ x, U x * f x := by
    simpa only [mul_comm] using h1.trans h2
  change (∫ x, (u x : ℂ) * 𝓕⁻ (𝓕 f) x) = ∫ x, (u x : ℂ) * f x at hpair
  simpa only [Complex.real_smul] using hpair

end Euclidean

/-- The landed coordinate inversion proof, localized to one continuity point. -/
theorem timeFourier_inversion_at {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hhf : Integrable (timeFourier f)) (t : Fin r → ℝ) (hc : ContinuousAt f t) : timeFourier (timeFourier f) (-t) = f t := by
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
  have hcont : ContinuousAt (fun x : EuclideanSpace ℝ (Fin r) => f (ofLp x)) (toLp 2 t) :=
    hc.comp (PiLp.continuous_ofLp 2 _).continuousAt
  have hinv := hfi.fourierInv_fourier_eq hhi hcont
  rw [timeFourier_eq_euclidean, he]
  rw [Real.fourierInv_eq_fourier_neg] at hinv
  simpa only [Function.comp_def, ofLp_toLp, toLp_neg] using hinv


/-- A nonnegative Fourier regularity norm bounds a function at each of its continuity points. -/
theorem enorm_le_timeFourierNorm_at {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    (f : (Fin r → ℝ) → ℂ) (t : Fin r → ℝ) (hc : ContinuousAt f t) :
    ‖f t‖ₑ ≤ timeFourierNorm θ f := by
  by_cases ht : timeFourierNorm θ f = ⊤
  · rw [ht]; exact le_top
  have hf := integrable_of_timeFourierNorm_lt_top (lt_top_iff_ne_top.mpr ht)
  have hff := integrable_timeFourier_of_norm_lt_top hθ (lt_top_iff_ne_top.mpr ht)
  rw [← timeFourier_inversion_at hf hff t hc]
  calc
    ‖timeFourier (timeFourier f) (-t)‖ₑ ≤ ∫⁻ ξ, ‖timeFourier f ξ‖ₑ := by
      change ‖∫ ξ, Real.fourierChar (-timePairing r ξ (-t)) • timeFourier f ξ‖ₑ ≤ _
      simpa only [Circle.enorm_smul] using
        (enorm_integral_le_lintegral_enorm
          (fun ξ => Real.fourierChar (-timePairing r ξ (-t)) • timeFourier f ξ))
    _ ≤ timeFourierNorm θ f := by
      rw [timeFourierNorm_eq_lintegral hf]
      apply lintegral_mono
      intro ξ
      have hw : (1 : ℝ≥0∞) ≤ timeWeight θ ξ := by
        simpa only [timeWeight, ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (Real.one_le_rpow (one_le_timeBracket ξ) hθ)
      simpa only [one_mul] using mul_le_mul_left hw ‖timeFourier f ξ‖ₑ

/-- Transport L1 Fourier inversion a.e. through the volume-preserving coordinate equivalence. -/
theorem timeFourier_inversion_ae {r : ℕ} {f : (Fin r → ℝ) → ℂ}
    (hf : Integrable f) (hhat : Integrable (timeFourier f)) :
    (fun t => timeFourier (timeFourier f) (-t)) =ᵐ[volume] f := by
  have hfi := (PiLp.volume_preserving_ofLp (Fin r)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin r → ℝ)).symm.measurableEmbedding (g := f) |>.mpr hf
  have he : (fun x : EuclideanSpace ℝ (Fin r) => timeFourier f (ofLp x)) =
      𝓕 (fun x : EuclideanSpace ℝ (Fin r) => f (ofLp x)) := by
    funext x
    simpa only [toLp_ofLp] using timeFourier_eq_euclidean f (ofLp x)
  have hhi := (PiLp.volume_preserving_ofLp (Fin r)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin r → ℝ)).symm.measurableEmbedding (g := timeFourier f) |>.mpr hhat
  simp only [Function.comp_def] at hhi
  rw [he] at hhi
  have hae := fourierInv_fourier_ae_eq_integrable hfi hhi
  have hcoord := (PiLp.volume_preserving_toLp (Fin r)).quasiMeasurePreserving.ae hae
  filter_upwards [hcoord] with t ht
  have hpoint : timeFourier (timeFourier f) (-t) =
      𝓕⁻ (𝓕 (fun x : EuclideanSpace ℝ (Fin r) => f (ofLp x))) (toLp 2 t) := by
    rw [timeFourier_eq_euclidean, he, Real.fourierInv_eq_fourier_neg]
    simp only [toLp_neg]
  rw [hpoint]
  simpa only [Function.comp_def, ofLp_toLp] using ht

/-- A finite nonnegative time norm supplies a continuous representative of the original slice. -/
theorem timeFourier_continuous_representative {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    (f : (Fin r → ℝ) → ℂ) (hf : timeFourierNorm θ f < ⊤) :
    Continuous (fun t => timeFourier (timeFourier f) (-t)) ∧
      (fun t => timeFourier (timeFourier f) (-t)) =ᵐ[volume] f := by
  have hi := integrable_of_timeFourierNorm_lt_top hf
  have hhat := integrable_timeFourier_of_norm_lt_top hθ hf
  exact ⟨(timeFourier_continuous hhat).comp continuous_neg, timeFourier_inversion_ae hi hhat⟩

end WaveTurbulence.Regref
