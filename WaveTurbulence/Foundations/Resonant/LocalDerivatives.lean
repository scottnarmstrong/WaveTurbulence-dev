/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.Derivatives
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Local smoothness of resonant integrals

A dominated differentiation lemma for scalar parameter families. The derivative
is taken through both levels of the hyperplane integral. Uniform decay of the
kernel and its parameter derivative provides all measurability and integrability
premises; none of these conclusions are additional assumptions.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- Dominated differentiation through the hyperplane delta integral. This is an
analytic helper, with uniform `DeltaKernel` decay for the family and its derivative. -/
theorem hasDerivAt_deltaInt_of_local_decay
    {F G : ℝ → Mom d → Mom d → ℝ} {A B : Mom d → ℝ}
    {b c : Mom d → Mom d} {M N : ℝ} {U : Set ℝ} (hU : IsOpen U) (hd : 0 < d)
    (hF : ∀ t ∈ U, DeltaKernel (F t) A b M)
    (hG : ∀ t ∈ U, DeltaKernel (G t) B c N)
    (hderiv : ∀ t ∈ U, ∀ ℓ x, HasDerivAt (fun s => F s ℓ x) (G t ℓ x) t)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (fun s => deltaInt (F s)) (deltaInt (G t)) t := by
  have hinner : ∀ ℓ : Mom d, ℓ ≠ 0 → ∀ s ∈ U,
      HasDerivAt (fun u => ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F u ℓ w)
        (∫ w : ↥(ℝ ∙ ℓ)ᗮ, G s ℓ w) s := by
    intro ℓ hℓ s hs
    have hdom := (hG s hs).integrable_slice_dom hℓ
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := U)
      (F := fun u (w : ↥(ℝ ∙ ℓ)ᗮ) => F u ℓ w)
      (F' := fun u (w : ↥(ℝ ∙ ℓ)ᗮ) => G u ℓ w)
      (hU.mem_nhds hs) ?_ ((hF s hs).integrable_perp hℓ) ?_ ?_ hdom ?_).2
    · filter_upwards [hU.mem_nhds hs] with u hu
      simpa only [zero_smul, zero_add] using
        ((hF u hu).continuous_slice ℓ 0).aestronglyMeasurable
    · simpa only [zero_smul, zero_add] using
        ((hG s hs).continuous_slice ℓ 0).aestronglyMeasurable
    · refine Eventually.of_forall fun w u hu => ?_
      rw [Real.norm_eq_abs]
      simpa only [zero_smul, zero_add] using (hG u hu).slice_bound hℓ 0 w
    · exact Eventually.of_forall fun w u hu => hderiv u hu ℓ w
  unfold deltaInt
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := U)
    (F := fun u (ℓ : Mom d) => (2 * ‖ℓ‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F u ℓ w)
    (F' := fun u (ℓ : Mom d) => (2 * ‖ℓ‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ)ᗮ, G u ℓ w)
    (hU.mem_nhds ht) ?_ ((hF t ht).integrable_outer hd) ?_ ?_
    ((hG t ht).integrable.const_mul (2⁻¹ * hypConst d N)) ?_).2
  · filter_upwards [hU.mem_nhds ht] with u hu
    exact ((hF u hu).integrable_outer hd).aestronglyMeasurable
  · exact ((hG t ht).integrable_outer hd).aestronglyMeasurable
  · filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    intro u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    have hb := (hG u hu).abs_sliceInt_le hℓ 0
    simp only [sliceInt, zero_smul, zero_add] at hb
    calc (2 * ‖ℓ‖)⁻¹ * |∫ w : ↥(ℝ ∙ ℓ)ᗮ, G u ℓ w|
        ≤ (2 * ‖ℓ‖)⁻¹ * (B ℓ * hypConst d N) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by rw [mul_inv]; ring
  · filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    intro u hu
    exact (hinner ℓ hℓ u hu).const_mul _


/-- All scalar parameter derivatives pass through the integral. Local uniform
polynomial decay may have a different integrable profile at each derivative order. -/
theorem contDiffOn_deltaInt_of_local_decay
    {F : ℕ → ℝ → Mom d → Mom d → ℝ} {A : ℕ → Mom d → ℝ}
    {b : ℕ → Mom d → Mom d} {M : ℕ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hd : 0 < d)
    (hF : ∀ n t, t ∈ U → DeltaKernel (F n t) (A n) (b n) (M n))
    (hderiv : ∀ n t, t ∈ U → ∀ ℓ x,
      HasDerivAt (fun s => F n s ℓ x) (F (n + 1) t ℓ x) t) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun t => deltaInt (F n t)) U := by
  have hD : ∀ n t, t ∈ U → HasDerivAt (fun s => deltaInt (F n s))
      (deltaInt (F (n + 1) t)) t := fun n _ ht =>
    hasDerivAt_deltaInt_of_local_decay hU hd (hF n) (hF (n + 1)) (hderiv n) ht
  have hfinite : ∀ m : ℕ, ∀ n : ℕ, ContDiffOn ℝ m (fun t => deltaInt (F n t)) U := by
    intro m
    induction m with
    | zero =>
      intro n
      exact contDiffOn_zero.mpr fun t ht => (hD n t ht).continuousAt.continuousWithinAt
    | succ m ih =>
      intro n
      rw [show ((m + 1 : ℕ) : ℕ∞ω) = (m : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun t ht => (hD n t ht).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
      apply (ih (n + 1)).congr
      intro t ht
      exact (hD n t ht).deriv
  exact contDiffOn_infty.mpr (fun m => hfinite m n)

/-- Smooth dependence for scalar families of three-momentum test kernels.
The zeroth member is the kernel and each next member is its parameter derivative. -/
theorem contDiffOn_resonantIntegral_of_local_decay
    {Ψ : ℕ → ℝ → Mom d → Mom d → Mom d → ℝ} {k : Mom d}
    {A : ℕ → Mom d → ℝ} {b : ℕ → Mom d → Mom d} {M : ℕ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hd : 0 < d)
    (hΨ : ∀ n t, t ∈ U → DeltaKernel (resonantKernel (Ψ n t) k) (A n) (b n) (M n))
    (hderiv : ∀ n t, t ∈ U → ∀ k₁ k₂ k₃,
      HasDerivAt (fun s => Ψ n s k₁ k₂ k₃) (Ψ (n + 1) t k₁ k₂ k₃) t) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun t => resonantIntegral (Ψ n t) k) U :=
  contDiffOn_deltaInt_of_local_decay hU hd hΨ (fun n t ht _ _ => hderiv n t ht _ _ _) n

end WaveTurbulence.Resonant
