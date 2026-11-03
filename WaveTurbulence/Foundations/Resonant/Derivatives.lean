/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.Integral
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation of resonant integrals

A dominated differentiation lemma for scalar parameter families. The derivative
is taken through both levels of the hyperplane integral. Uniform decay of the
kernel and its parameter derivative provides all measurability and integrability
premises; none of these conclusions are additional assumptions.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace WaveTurbulence

variable {d : ℕ}

/-- Dominated differentiation through the hyperplane delta integral. This is an
analytic helper, with uniform `DeltaKernel` decay for the family and its derivative. -/
theorem hasDerivAt_deltaInt_of_decay
    {F G : ℝ → Mom d → Mom d → ℝ} {A B : Mom d → ℝ}
    {b c : Mom d → Mom d} {M N : ℝ} (hd : 0 < d)
    (hF : ∀ t, DeltaKernel (F t) A b M) (hG : ∀ t, DeltaKernel (G t) B c N)
    (hderiv : ∀ t ℓ x, HasDerivAt (fun s => F s ℓ x) (G t ℓ x) t) (t : ℝ) :
    HasDerivAt (fun s => deltaInt (F s)) (deltaInt (G t)) t := by
  have hinner : ∀ ℓ : Mom d, ℓ ≠ 0 → ∀ s : ℝ,
      HasDerivAt (fun u => ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F u ℓ w)
        (∫ w : ↥(ℝ ∙ ℓ)ᗮ, G s ℓ w) s := by
    intro ℓ hℓ s
    have hdom := (hG s).integrable_slice_dom hℓ
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
      (F := fun u (w : ↥(ℝ ∙ ℓ)ᗮ) => F u ℓ w)
      (F' := fun u (w : ↥(ℝ ∙ ℓ)ᗮ) => G u ℓ w)
      Filter.univ_mem ?_ ((hF s).integrable_perp hℓ) ?_ ?_ hdom ?_).2
    · refine Eventually.of_forall fun u => ?_
      simpa only [zero_smul, zero_add] using
        ((hF u).continuous_slice ℓ 0).aestronglyMeasurable
    · simpa only [zero_smul, zero_add] using
        ((hG s).continuous_slice ℓ 0).aestronglyMeasurable
    · refine Eventually.of_forall fun w u _ => ?_
      rw [Real.norm_eq_abs]
      simpa only [zero_smul, zero_add] using (hG u).slice_bound hℓ 0 w
    · exact Eventually.of_forall fun w u _ => hderiv u ℓ w
  unfold deltaInt
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun u (ℓ : Mom d) => (2 * ‖ℓ‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F u ℓ w)
    (F' := fun u (ℓ : Mom d) => (2 * ‖ℓ‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ)ᗮ, G u ℓ w)
    Filter.univ_mem ?_ ((hF t).integrable_outer hd) ?_ ?_
    ((hG t).integrable.const_mul (2⁻¹ * hypConst d N)) ?_).2
  · exact Eventually.of_forall fun u => ((hF u).integrable_outer hd).aestronglyMeasurable
  · exact ((hG t).integrable_outer hd).aestronglyMeasurable
  · filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    intro u _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    have hb := (hG u).abs_sliceInt_le hℓ 0
    simp only [sliceInt, zero_smul, zero_add] at hb
    calc (2 * ‖ℓ‖)⁻¹ * |∫ w : ↥(ℝ ∙ ℓ)ᗮ, G u ℓ w|
        ≤ (2 * ‖ℓ‖)⁻¹ * (B ℓ * hypConst d N) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by rw [mul_inv]; ring
  · filter_upwards [DeltaKernel.ae_ne_zero hd] with ℓ hℓ
    intro u _
    exact (hinner ℓ hℓ u).const_mul _

/-- Differentiation of a family of three-momentum kernels under the resonant
integral. Applying this to `Ψ t k₁ k₂ k₃ = Φ (k₁+t•v) (k₂+t•v) (k₃+t•v)`
gives differentiation in the external momentum in direction `v`. -/
theorem hasDerivAt_resonantIntegral_of_decay
    {Ψ Ψ' : ℝ → Mom d → Mom d → Mom d → ℝ} {k : Mom d}
    {A B : Mom d → ℝ} {b c : Mom d → Mom d} {M N : ℝ} (hd : 0 < d)
    (hΨ : ∀ t, DeltaKernel (resonantKernel (Ψ t) k) A b M)
    (hΨ' : ∀ t, DeltaKernel (resonantKernel (Ψ' t) k) B c N)
    (hderiv : ∀ t k₁ k₂ k₃, HasDerivAt (fun s => Ψ s k₁ k₂ k₃) (Ψ' t k₁ k₂ k₃) t)
    (t : ℝ) :
    HasDerivAt (fun s => resonantIntegral (Ψ s) k) (resonantIntegral (Ψ' t) k) t :=
  hasDerivAt_deltaInt_of_decay hd hΨ hΨ' (fun u _ _ => hderiv u _ _ _) t

end WaveTurbulence
