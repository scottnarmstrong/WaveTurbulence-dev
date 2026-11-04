/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.DeltaReading

/-!
# Integrable slices of decaying resonant kernels

The measure-preserving normal/hyperplane coordinates and Fubini give an
integrable slice integral. Its L¹ norm is bounded uniformly in the kernel's
translation center by the full-dimensional radial decay integral. These are
the slice tail estimates for the decaying principal-value characterization
(TARGET (C.5); B2 REQUIRED F-5).
-/

public section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace WaveTurbulence.Resonant

variable {d : ℕ} {F : Mom d → Mom d → ℝ} {A : Mom d → ℝ}
  {a : Mom d → Mom d} {N : ℝ}

/-- A translated decay profile gives a center-independent full-dimensional L¹ bound. -/
theorem integral_norm_right_le (hF : DeltaKernel F A a N) (ℓ : Mom d) :
    (∫ x : Mom d, ‖F ℓ x‖) ≤ A ℓ * hypConst (d+1) N := by
  have hfr : (Module.finrank ℝ (Mom d) : ℝ) < N := by
    rw [finrank_euclideanSpace_fin]
    exact hF.dim
  have hdom := ((integrable_one_add_norm (E := Mom d) (μ := volume) hfr).comp_add_left
    (a ℓ)).const_mul (A ℓ)
  calc
    (∫ x : Mom d, ‖F ℓ x‖) ≤
        ∫ x : Mom d, A ℓ * (1+‖a ℓ+x‖)^(-N) := by
      apply integral_mono (hF.integrable_right ℓ).norm hdom
      intro x
      simpa only [Real.norm_eq_abs] using hF.bound ℓ x
    _ = A ℓ * ∫ x : Mom d, (1+‖x‖)^(-N) := by
      rw [integral_const_mul,
        integral_add_left_eq_self (fun x : Mom d => (1+‖x‖)^(-N)) (a ℓ)]
    _ = A ℓ * hypConst (d+1) N := by
      exact (congrArg (fun m : ℕ => A ℓ * ∫ x : Mom m, (1+‖x‖)^(-N))
        (Nat.add_sub_cancel d 1)).symm

private theorem integrable_slice_coordinates (hF : DeltaKernel F A a N)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Integrable (F ℓ ∘ sliceEquiv hℓ)
      ((volume : Measure ℝ).prod (volume : Measure ↥(ℝ ∙ ℓ)ᗮ)) := by
  exact (measurePreserving_sliceEquiv hℓ).integrable_comp_emb
    (sliceEquiv hℓ).measurableEmbedding |>.mpr (hF.integrable_right ℓ)

/-- Fubini integrability of the actual hyperplane slice integral. -/
theorem integrable_sliceInt (hF : DeltaKernel F A a N) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Integrable (sliceInt F ℓ) := by
  have h := (integrable_slice_coordinates hF hℓ).integral_prod_left
  unfold sliceInt
  simpa only [Function.comp_def,sliceEquiv_apply] using h

/-- The slice L¹ norm is bounded by the kernel L¹ norm, hence by a uniform decay constant. -/
theorem integral_norm_sliceInt_le (hF : DeltaKernel F A a N)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    (∫ t : ℝ, ‖sliceInt F ℓ t‖) ≤ A ℓ * hypConst (d+1) N := by
  have hdom := (integrable_slice_coordinates hF hℓ).integral_norm_prod_left
  simp only [Function.comp_def,sliceEquiv_apply] at hdom
  calc
    (∫ t : ℝ, ‖sliceInt F ℓ t‖) ≤
        ∫ t : ℝ, ∫ w : ↥(ℝ ∙ ℓ)ᗮ, ‖F ℓ (t • unitVec ℓ + w)‖ := by
      apply integral_mono (integrable_sliceInt hF hℓ).norm hdom
      intro t
      exact norm_integral_le_integral_norm _
    _ = ∫ x : Mom d, ‖F ℓ x‖ :=
      (integral_eq_integral_slice hℓ (hF.integrable_right ℓ).norm).symm
    _ ≤ A ℓ * hypConst (d+1) N := integral_norm_right_le hF ℓ

end WaveTurbulence.Resonant
