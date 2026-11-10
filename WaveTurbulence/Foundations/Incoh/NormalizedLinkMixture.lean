/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.ProductLinkMixture

/-!
# Normalized literal link-mixture mass and incoherence decay

The amplitude contains the source coupling and all actual localized link
factors. The only hypotheses on its clock domain are measurability.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Literal source coupling times the selected-link phase/internal-clock amplitude. -/
@[expose] def normalizedLinkMixtureAmplitude {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (J : Finset (Fin n)) (S : Set (Fin n → LinkMixturePoint d)) (z : Fin n → LinkMixturePoint d) : ℂ :=
  (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ) *
    productLinkMixtureAmplitude L γ δ Q J S z

theorem stronglyMeasurable_normalizedLinkMixtureAmplitude {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    StronglyMeasurable (normalizedLinkMixtureAmplitude L γ δ Q J S) :=
  (stronglyMeasurable_productLinkMixtureAmplitude hL γ δ Q J hS).const_mul _

theorem integrable_normalizedLinkMixtureAmplitude {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    Integrable (normalizedLinkMixtureAmplitude L γ δ Q J S) (productLinkMixtureMeasure d n J) :=
  (integrable_productLinkMixtureAmplitude hL γ δ Q J hS).const_mul _

/-- Actual amplitude mass is bounded by the previously proved normalized replacement product. -/
theorem lintegral_normalizedLinkMixtureAmplitude_le {d n : ℕ} {L δ : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (γ : ℝ) (Q : Fin n → LayerLink d) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    (∫⁻ z, ‖normalizedLinkMixtureAmplitude L γ δ Q J S z‖ₑ ∂productLinkMixtureMeasure d n J) ≤
      normalizedReplacedLinkMass L γ δ Q J := by
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  have hnorm : ‖((((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ))‖ₑ =
      ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  simp_rw [normalizedLinkMixtureAmplitude, enorm_mul, hnorm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl (lintegral_productLinkMixtureAmplitude_le hL γ δ Q J hS)

end WaveTurbulence.Incoh
