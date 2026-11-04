/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.FrequencySplit
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Product domination by the actual link masses

TARGET (incohproof16). The source time domain is dominated by the product
of its link boxes, using the proved integrability of each literal factor.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The link mass is the real absolute integral, transported to the nonnegative scalars. -/
theorem layerLinkMass_eq_ofReal_integral {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) :
    layerLinkMass L (δ * L ^ (2 * γ)) Q =
      ENNReal.ofReal (∫ t in linkBox Q, ‖linkTimeFactor L γ δ Q t‖) := by
  change (∫⁻ t in linkBox Q,
    ‖linkLatticeSum L (((Q.orientation : ℤ) : ℝ) * (δ * L ^ (2 * γ)) * (t 0 - t 1)) Q.toLinkParameters‖ₑ) = _
  have heq (t : Fin 2 → ℝ) :
      linkLatticeSum L (((Q.orientation : ℤ) : ℝ) * (δ * L ^ (2 * γ)) * (t 0 - t 1)) Q.toLinkParameters =
        linkTimeFactor L γ δ Q t := by
    unfold linkTimeFactor
    congr 1
    ring
  simp_rw [heq, ← ofReal_norm]
  exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_linkTimeFactor hL γ δ Q).norm
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)).symm

/-- Actual kernel integration over every source subdomain is bounded by the product of literal masses. -/
theorem enorm_linkProduct_integral_le {d n : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) {I : Set (Fin n → Fin 2 → ℝ)}
    (hI : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    ‖∫ t in I, ∏ i, linkTimeFactor L γ δ (Q i) (t i)‖ₑ ≤
      ∏ i, layerLinkMass L (δ * L ^ (2 * γ)) (Q i) := by
  rw [← ofReal_norm]
  apply (ENNReal.ofReal_le_ofReal (norm_linkProduct_integral_le hL γ δ Q hI)).trans_eq
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg fun _ => norm_nonneg _)]
  apply Finset.prod_congr rfl
  intro i _
  exact (layerLinkMass_eq_ofReal_integral hL γ δ (Q i)).symm

/-- Absolute product domination, the form needed for the root-density L¹ estimate. -/
theorem lintegral_linkProduct_enorm_le {d n : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) {I : Set (Fin n → Fin 2 → ℝ)}
    (hI : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    (∫⁻ t in I, ‖∏ i, linkTimeFactor L γ δ (Q i) (t i)‖ₑ) ≤
      ∏ i, layerLinkMass L (δ * L ^ (2 * γ)) (Q i) := by
  have hi := (integrableOn_linkProduct hL γ δ Q hI).norm
  have heq : (∫⁻ t in I, ‖∏ i, linkTimeFactor L γ δ (Q i) (t i)‖ₑ) =
      ENNReal.ofReal (∫ t in I, ∏ i, ‖linkTimeFactor L γ δ (Q i) (t i)‖) := by
    simp_rw [← ofReal_norm, norm_prod]
    exact (ofReal_integral_eq_lintegral_ofReal (by simpa only [norm_prod] using hi)
      (Filter.Eventually.of_forall fun t => Finset.prod_nonneg fun _ _ => norm_nonneg _)).symm
  rw [heq]
  apply (ENNReal.ofReal_le_ofReal (setIntegral_pi_product_norm_le hI
    (fun i => integrableOn_linkTimeFactor hL γ δ (Q i)))).trans_eq
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg fun _ => norm_nonneg _)]
  exact Finset.prod_congr rfl fun i _ => (layerLinkMass_eq_ofReal_integral hL γ δ (Q i)).symm

end WaveTurbulence.Incoh
