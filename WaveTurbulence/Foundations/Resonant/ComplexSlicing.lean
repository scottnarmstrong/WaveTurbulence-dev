/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.LocalizedSlices
public import WaveTurbulence.Foundations.Resonant.CentralFourier
public import WaveTurbulence.Foundations.Resonant.PrincipalValueSlices
public import WaveTurbulence.Foundations.Resonant.PrincipalValueComplex

/-!
# Complex Fourier integrals in hyperplane coordinates

The real slicing formula extends to Bochner integrals with any normed real
codomain. In particular it separates the tangential Fourier phase from the
normal frequency in a truncated inverse bilinear resonance.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- Vector-valued extension of the landed real hyperplane disintegration formula. -/
theorem integral_eq_integral_slice_vector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) {g : Mom d → E} (hg : Integrable g) :
    (∫ y, g y) = ∫ t : ℝ, ∫ w : ↥(ℝ ∙ ℓ)ᗮ, g (t • unitVec ℓ + w) := by
  have hmp := measurePreserving_sliceEquiv hℓ
  rw [← hmp.integral_comp' g]
  have hi : Integrable (g ∘ sliceEquiv hℓ) (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) :=
    hmp.integrable_comp_emb (sliceEquiv hℓ).measurableEmbedding |>.mpr hg
  rw [show (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) = volume.prod volume from rfl] at hi ⊢
  have h := integral_prod _ hi
  simpa only [Function.comp_def, sliceEquiv_apply] using h

/-- Addition of phases becomes multiplication. -/
theorem unitPhase_add (η s t : ℝ) :
    unitPhase η (s + t) = unitPhase η s * unitPhase η t := by
  simp only [unitPhase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- The normal and tangential parts of the Fourier phase. -/
theorem unitPhase_inner_slice (η : Mom d) {ℓ : Mom d} (t : ℝ) (w : ↥(ℝ ∙ ℓ)ᗮ) :
    unitPhase 1 ⟪η, t • unitVec ℓ + (w : Mom d)⟫_ℝ =
      unitPhase ⟪η, unitVec ℓ⟫_ℝ t * unitPhase 1 ⟪η, (w : Mom d)⟫_ℝ := by
  rw [inner_add_right, inner_smul_right, unitPhase_add]
  congr 1
  simp only [unitPhase, one_mul, mul_comm]

/-- A finite truncated inverse bilinear integral with Fourier phase in the second variable. -/
@[expose] noncomputable def bilinearInvFourierInner (χ : ℝ → ℝ) (μ : ℝ)
    (f : Mom d → ℂ) (ℓ η : Mom d) : ℂ :=
  ∫ y : Mom d, (((1 - χ (μ * ⟪ℓ, y⟫_ℝ)) / ⟪ℓ, y⟫_ℝ : ℝ) : ℂ) *
    (f y * unitPhase 1 ⟪η, y⟫_ℝ)

/-- Every finite localized bilinear integral is absolutely integrable. -/
theorem integrable_bilinearInvFourierInner
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ : ℝ)
    {f : Mom d → ℂ} {b : Mom d} {R : ℝ}
    (hc : Continuous f) (hs : ∀ y, R < ‖y - b‖ → f y = 0) (ℓ η : Mom d) :
    Integrable (fun y : Mom d => (((1 - χ (μ * ⟪ℓ, y⟫_ℝ)) / ⟪ℓ, y⟫_ℝ : ℝ) : ℂ) *
      (f y * unitPhase 1 ⟪η, y⟫_ℝ)) := by
  have hfi := integrable_localized_amplitude hc hs
  obtain ⟨C, _, hC⟩ := hχ.exists_bound_div μ
  have hgc : Continuous (fun y : Mom d =>
      ((((1 - χ (μ * ⟪ℓ, y⟫_ℝ)) / ⟪ℓ, y⟫_ℝ : ℝ) : ℂ)) * unitPhase 1 ⟪η, y⟫_ℝ) :=
    (Complex.continuous_ofReal.comp ((hχ.continuous_div μ).comp
      (continuous_const.inner continuous_id))).mul
        ((continuous_unitPhase 1).comp (continuous_const.inner continuous_id))
  have hi := hfi.mul_bdd (c := C) hgc.aestronglyMeasurable (Eventually.of_forall fun y => by
    rw [norm_mul, norm_unitPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hC _)
  exact hi.congr (Eventually.of_forall fun y => by ring)

/-- The bilinear inverse integral is a one-dimensional principal-value Fourier
truncation of a localized tangential slice. -/
theorem bilinearInvFourierInner_eq
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ : ℝ)
    {f : Mom d → ℂ} {b : Mom d} {R : ℝ}
    (hc : Continuous f) (hs : ∀ y, R < ‖y - b‖ → f y = 0)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) (η : Mom d) :
    bilinearInvFourierInner χ μ f ℓ η = (‖ℓ‖⁻¹ : ℝ) *
      pvTruncationComplex χ (μ * ‖ℓ‖) (fun t =>
        localizedSlice f (ℓ := ℓ) (fun w => unitPhase 1 ⟪η, (w : Mom d)⟫_ℝ) t *
          unitPhase ⟪η, unitVec ℓ⟫_ℝ t) := by
  rw [bilinearInvFourierInner,
    integral_eq_integral_slice_vector hℓ (integrable_bilinearInvFourierInner hχ μ hc hs ℓ η)]
  have hin : ∀ t (w : ↥(ℝ ∙ ℓ)ᗮ), ⟪ℓ, t • unitVec ℓ + (w : Mom d)⟫_ℝ = t * ‖ℓ‖ := by
    intro t w
    rw [inner_add_right, inner_smul_right, inner_unitVec_self,
      inner_eq_zero_of_mem_perp w, add_zero]
  simp_rw [hin, unitPhase_inner_slice]
  have hinner : ∀ t : ℝ,
      (∫ w : ↥(ℝ ∙ ℓ)ᗮ,
        (((1 - χ (μ * (t * ‖ℓ‖))) / (t * ‖ℓ‖) : ℝ) : ℂ) *
          (f (t • unitVec ℓ + w) *
            (unitPhase ⟪η, unitVec ℓ⟫_ℝ t * unitPhase 1 ⟪η, (w : Mom d)⟫_ℝ))) =
        (((1 - χ (μ * (t * ‖ℓ‖))) / (t * ‖ℓ‖) : ℝ) : ℂ) *
          (localizedSlice f (ℓ := ℓ) (fun w => unitPhase 1 ⟪η, (w : Mom d)⟫_ℝ) t *
            unitPhase ⟪η, unitVec ℓ⟫_ℝ t) := by
    intro t
    rw [localizedSlice, ← integral_mul_const, ← integral_const_mul]
    congr 1
    funext w
    ring
  simp_rw [hinner]
  rw [pvTruncationComplex, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hq : (1 - χ (μ * (t * ‖ℓ‖))) / (t * ‖ℓ‖) =
      ‖ℓ‖⁻¹ * ((1 - χ ((μ * ‖ℓ‖) * t)) / t) := by
    simp only [div_eq_mul_inv, mul_inv]
    ring_nf
  simp only
  rw [hq]
  push_cast
  ring

end WaveTurbulence.Resonant
