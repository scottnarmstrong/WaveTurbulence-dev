/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.RootEnvelope
public import WaveTurbulence.Foundations.Incoh.RootDensityL1

/-!
# The actual root density is dominated by the root-link envelope

TARGET (incohproof18). The proof retains the source time-order indicator,
uses the literal trivial bound only at root links, and integrates the
proved pointwise envelope along the actual root fibers.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Root-link removal dominates the literal indicator times the oscillatory product. -/
theorem RootCoordinates.enorm_indicator_product_le_envelope {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (t : Fin n → Fin 2 → ℝ) :
    ‖I.indicator (fun t => ∏ i, linkTimeFactor L γ δ (Q i) (t i)) t‖ₑ ≤ R.envelope L γ δ Q t := by
  by_cases ht : t ∈ I
  · rw [Set.indicator_of_mem (s := I) ht, envelope, Set.indicator_of_mem (hbox ht)]
    rw [← ofReal_norm, norm_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
    apply Finset.prod_le_prod
    intro i _
    by_cases hi : i ∈ R.rootLinks
    · rw [envelopeFactor, ite_eq_left hi]
      apply ENNReal.ofReal_le_ofReal
      exact norm_linkLatticeSum_le hL _ _
    · rw [envelopeFactor, ite_eq_right hi, ofReal_norm]
  · rw [Set.indicator_of_notMem (s := I) ht, enorm_zero]
    exact bot_le

/-- The actual normalized root marginal is bounded by the integral of its root-link envelope. -/
theorem RootCoordinates.enorm_linkDensity_le_envelope {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    {L δ : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (γ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (t : Fin r → ℝ) :
    ‖R.linkDensity L γ δ Q I t‖ₑ ≤
      ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) * ∫⁻ v, R.envelope L γ δ Q v := by
  have hLp := zero_lt_one.trans_le hL
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  have hnorm : ‖((((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ))‖ₑ =
      ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) := by
    rw [← ofReal_norm]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    _ ≤ ∫⁻ u, ‖normalizedLinkIntegrand L γ δ Q I (R.equiv.symm (t, u))‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        R.envelope L γ δ Q (R.equiv.symm (t, u)) := by
      apply lintegral_mono
      intro u
      dsimp only
      rw [normalizedLinkIntegrand, enorm_mul, hnorm]
      exact mul_le_mul' le_rfl (R.enorm_indicator_product_le_envelope hL γ δ Q hbox _)
    _ = ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        ∫⁻ u, R.envelope L γ δ Q (R.equiv.symm (t, u)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (R.lintegral_envelope_fiber_le hLp γ δ Q t)

end WaveTurbulence.Incoh
