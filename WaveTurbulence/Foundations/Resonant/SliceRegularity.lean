/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.Integral
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Regularity and support of hyperplane slices

Normal derivatives of a smooth decaying kernel pass through the hyperplane
integral. A support bound in the second momentum gives compact support in the
normal parameter, as required for principal-value cancellation.
-/

public section

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace NNReal

namespace WaveTurbulence

variable {d : ℕ}

/-- The normal parameter cannot exceed the norm of the sliced point. -/
theorem abs_le_norm_smul_unitVec_add {ℓ : Mom d} (hℓ : ℓ ≠ 0) (t : ℝ)
    (w : ↥(ℝ ∙ ℓ)ᗮ) : |t| ≤ ‖t • unitVec ℓ + (w : Mom d)‖ := by
  have h := norm_sq_smul_unitVec_add hℓ t w
  nlinarith [sq_nonneg ‖(w : Mom d)‖, norm_nonneg (t • unitVec ℓ + (w : Mom d)),
    abs_nonneg t, sq_abs t]

/-- A support radius in the second momentum bounds the support of every slice. -/
theorem sliceInt_eq_zero_of_radius {F : Mom d → Mom d → ℝ} {R : ℝ}
    (hs : ∀ ℓ x, R < ‖x‖ → F ℓ x = 0) {ℓ : Mom d} (hℓ : ℓ ≠ 0)
    {t : ℝ} (ht : R < |t|) : sliceInt F ℓ t = 0 := by
  unfold sliceInt
  have hz : (fun w : ↥(ℝ ∙ ℓ)ᗮ => F ℓ (t • unitVec ℓ + w)) = fun _ => 0 := by
    funext w
    exact hs ℓ _ (ht.trans_le (abs_le_norm_smul_unitVec_add hℓ t w))
  rw [hz, integral_zero]

theorem hasCompactSupport_sliceInt {F : Mom d → Mom d → ℝ} {R : ℝ}
    (hs : ∀ ℓ x, R < ‖x‖ → F ℓ x = 0) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    HasCompactSupport (sliceInt F ℓ) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-R) R) isCompact_Icc
  intro t ht
  by_contra hn
  have hout : R < |t| := by
    by_contra hnot
    exact hn (abs_le.mp (le_of_not_gt hnot))
  exact ht (sliceInt_eq_zero_of_radius hs hℓ hout)

/-- A normal derivative is dominated by an integrable hyperplane profile. -/
theorem normalDeriv_bound
    {D : Mom d → Mom d → Mom d →L[ℝ] ℝ} {B : Mom d → ℝ}
    {b : Mom d → Mom d} {M : ℝ}
    (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) (t : ℝ) (w : ↥(ℝ ∙ ℓ)ᗮ) :
    |D ℓ (t • unitVec ℓ + w) (unitVec ℓ)| ≤
      B ℓ * (1 + ‖((perpPart ℓ (b ℓ) + w : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)‖) ^ (-M) := by
  calc |D ℓ (t • unitVec ℓ + w) (unitVec ℓ)|
      ≤ ‖D ℓ (t • unitVec ℓ + w)‖ * ‖unitVec ℓ‖ := by
        simpa only [Real.norm_eq_abs] using
          (D ℓ (t • unitVec ℓ + w)).le_opNorm (unitVec ℓ)
    _ = ‖D ℓ (t • unitVec ℓ + w)‖ := by rw [norm_unitVec hℓ, mul_one]
    _ ≤ _ := by
      simpa only [abs_of_nonneg (norm_nonneg _)] using hgrad.slice_bound hℓ t w

/-- Differentiation through a hyperplane slice for a smooth decaying kernel. -/
theorem hasDerivAt_sliceInt
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M : ℝ}
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ))
    (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) (t : ℝ) :
    HasDerivAt (sliceInt F ℓ)
      (∫ w : ↥(ℝ ∙ ℓ)ᗮ, D ℓ (t • unitVec ℓ + w) (unitVec ℓ)) t := by
  unfold sliceInt
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun s (w : ↥(ℝ ∙ ℓ)ᗮ) => F ℓ (s • unitVec ℓ + w))
    (F' := fun s (w : ↥(ℝ ∙ ℓ)ᗮ) => D ℓ (s • unitVec ℓ + w) (unitVec ℓ))
    Filter.univ_mem ?_ (hF.integrable_slice hℓ t) ?_ ?_
    (hgrad.integrable_slice_dom hℓ) ?_).2
  · exact Eventually.of_forall fun s => (hF.continuous_slice ℓ s).aestronglyMeasurable
  · exact (((hDc ℓ).comp (continuous_const.add continuous_subtype_val)).clm_apply
      continuous_const).aestronglyMeasurable
  · exact Eventually.of_forall fun w s _ => by
      rw [Real.norm_eq_abs]
      exact normalDeriv_bound hgrad hℓ s w
  · refine Eventually.of_forall fun w s _ => ?_
    have hp : HasDerivAt (fun u : ℝ => u • unitVec ℓ + (w : Mom d)) (unitVec ℓ) s := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id s).smul_const (unitVec ℓ)).add_const (w : Mom d)
    exact (hD ℓ _).comp_hasDerivAt s hp

/-- Uniform bound for the normal derivative of the slice. -/
theorem abs_normalDeriv_sliceInt_le
    {D : Mom d → Mom d → Mom d →L[ℝ] ℝ} {B : Mom d → ℝ}
    {b : Mom d → Mom d} {M : ℝ}
    (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) (t : ℝ) :
    |∫ w : ↥(ℝ ∙ ℓ)ᗮ, D ℓ (t • unitVec ℓ + w) (unitVec ℓ)| ≤
      B ℓ * hypConst d M := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hgrad.integrable_slice_dom hℓ)
    (Eventually.of_forall fun w => ?_)).trans_eq ?_
  · rw [Real.norm_eq_abs]
    exact normalDeriv_bound hgrad hℓ t w
  · rw [integral_const_mul, integral_one_add_norm_perp hℓ M]

/-- The slice is Lipschitz, with a bound obtained from decay of the kernel gradient. -/
theorem lipschitzWith_sliceInt
    {F : Mom d → Mom d → ℝ} {D : Mom d → Mom d → Mom d →L[ℝ] ℝ}
    {A B : Mom d → ℝ} {a b : Mom d → Mom d} {N M : ℝ}
    (hF : DeltaKernel F A a N) (hgrad : DeltaKernel (fun ℓ x => ‖D ℓ x‖) B b M)
    (hDc : ∀ ℓ, Continuous (D ℓ))
    (hD : ∀ ℓ x, HasFDerivAt (F ℓ) (D ℓ x) x)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    LipschitzWith ⟨B ℓ * hypConst d M,
      mul_nonneg (hgrad.A_nonneg ℓ) (hypConst_nonneg d M)⟩ (sliceInt F ℓ) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (hasDerivAt_sliceInt hF hgrad hDc hD hℓ t).differentiableAt)
  intro t
  rw [(hasDerivAt_sliceInt hF hgrad hDc hD hℓ t).deriv]
  exact_mod_cast abs_normalDeriv_sliceInt_le hgrad hℓ t

end WaveTurbulence
