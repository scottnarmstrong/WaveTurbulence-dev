/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.MixedNorm
public import WaveTurbulence.Foundations.Fourier.TimeEuclidean
public import WaveTurbulence.Foundations.Fourier.TimeWeights
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Order-zero mixed Fourier norms with arbitrary vector parameters

TARGET L581, L589: the supremum over vector arguments is inside the
frequency integral. No measure or topology on the vector-variable type is
needed. In particular the definition applies to every finite-dimensional
vector space and to finite products of such spaces. Nonintegrable time
slices give infinity, matching the landed Fourier norms.
-/

public section

namespace WaveTurbulence.Fourier
open MeasureTheory Set
open scoped ENNReal

/-- The pointwise envelope of the time Fourier transforms of all vector slices. -/
@[expose] noncomputable def mixedFourierEnvelope00 {r : ℕ} {V : Type*}
    (F : (Fin r → ℝ) → V → ℂ) (ξ : Fin r → ℝ) : ℝ≥0∞ :=
  ⨆ v, ‖timeFourier (fun t => F t v) ξ‖ₑ

/-- TARGET `𝔛^{θ,0,0}` for arbitrary vector arguments, with an integrability guard. -/
@[expose] noncomputable def mixedFourierNorm00 {r : ℕ} {V : Type*} (θ : ℝ)
    (F : (Fin r → ℝ) → V → ℂ) : ℝ≥0∞ := by
  classical
  exact if ∀ v, Integrable (fun t => F t v) then
    ∫⁻ ξ, timeWeight θ ξ * mixedFourierEnvelope00 F ξ else ⊤

/-- TARGET `locnorm`: extensions agree at every point of `B × K`. -/
@[expose] noncomputable def mixedRestrictionNorm00 {r : ℕ} {V : Type*} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set V) (F : B → K → ℂ) : ℝ≥0∞ :=
  ⨅ (G : (Fin r → ℝ) → V → ℂ) (_ : ∀ (t : B) (v : K), G t v = F t v), mixedFourierNorm00 θ G

theorem mixedFourierNorm00_eq_lintegral {r : ℕ} {V : Type*} {θ : ℝ}
    {F : (Fin r → ℝ) → V → ℂ} (hF : ∀ v, Integrable (fun t => F t v)) :
    mixedFourierNorm00 θ F = ∫⁻ ξ, timeWeight θ ξ * mixedFourierEnvelope00 F ξ := by
  rw [mixedFourierNorm00, ite_eq_left hF]

theorem mixedFourierNorm00_of_not_integrable {r : ℕ} {V : Type*} {θ : ℝ}
    {F : (Fin r → ℝ) → V → ℂ} (hF : ¬ ∀ v, Integrable (fun t => F t v)) :
    mixedFourierNorm00 θ F = ⊤ := by
  simp only [mixedFourierNorm00, hF, ↓reduceIte]

theorem integrable_of_mixedFourierNorm00_lt_top {r : ℕ} {V : Type*} {θ : ℝ}
    {F : (Fin r → ℝ) → V → ℂ} (hF : mixedFourierNorm00 θ F < ⊤) (v : V) :
    Integrable (fun t => F t v) := by
  by_contra h
  have hn : ¬ ∀ v, Integrable (fun t => F t v) := fun hF => h (hF v)
  rw [mixedFourierNorm00_of_not_integrable hn] at hF
  exact lt_irrefl _ hF

/-- An arbitrary supremum of continuous Fourier slices is lower semicontinuous. -/
theorem lowerSemicontinuous_mixedFourierEnvelope00 {r : ℕ} {V : Type*}
    {F : (Fin r → ℝ) → V → ℂ} (hF : ∀ v, Integrable (fun t => F t v)) :
    LowerSemicontinuous (mixedFourierEnvelope00 F) :=
  lowerSemicontinuous_iSup (fun v =>
    (continuous_enorm.comp (timeFourier_continuous (hF v))).lowerSemicontinuous)

theorem measurable_mixedFourierEnvelope00 {r : ℕ} {V : Type*}
    {F : (Fin r → ℝ) → V → ℂ} (hF : ∀ v, Integrable (fun t => F t v)) :
    Measurable (mixedFourierEnvelope00 F) :=
  (lowerSemicontinuous_mixedFourierEnvelope00 hF).measurable

theorem timeFourierNorm_slice_le_mixedFourierNorm00 {r : ℕ} {V : Type*} (θ : ℝ)
    (F : (Fin r → ℝ) → V → ℂ) (v : V) :
    timeFourierNorm θ (fun t => F t v) ≤ mixedFourierNorm00 θ F := by
  by_cases hF : ∀ v, Integrable (fun t => F t v)
  · rw [timeFourierNorm_eq_lintegral (hF v), mixedFourierNorm00_eq_lintegral hF]
    exact lintegral_mono (fun ξ => mul_le_mul_right (le_iSup (fun v => ‖timeFourier (fun t => F t v) ξ‖ₑ) v) _)
  · rw [mixedFourierNorm00_of_not_integrable hF]
    exact le_top

@[simp] theorem mixedFourierNorm00_zero {r : ℕ} {V : Type*} (θ : ℝ) :
    mixedFourierNorm00 θ (fun (_ : Fin r → ℝ) (_ : V) => 0) = 0 := by
  simp [mixedFourierNorm00, mixedFourierEnvelope00, timeFourier_zero]

/-- With one vector argument this is exactly the scalar time Fourier norm. -/
theorem mixedFourierNorm00_unit {r : ℕ} (θ : ℝ) (f : (Fin r → ℝ) → ℂ) :
    mixedFourierNorm00 θ (fun t (_ : Unit) => f t) = timeFourierNorm θ f := by
  have he : (∀ _v : Unit, Integrable (fun t => f t)) ↔ Integrable f :=
    ⟨fun h => h (), fun h _ => h⟩
  unfold mixedFourierNorm00 timeFourierNorm
  rw [he]
  simp only [mixedFourierEnvelope00, iSup_unique]

end WaveTurbulence.Fourier
