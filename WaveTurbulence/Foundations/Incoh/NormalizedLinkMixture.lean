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

/-- TARGET's full incoherence gain for the literal selected-link mixture amplitude. -/
theorem exists_normalizedLinkMixtureAmplitude_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ k : ℕ, ∀ J : Finset (Fin n), J.card ≤ k →
        ∀ S : Set (Fin n → LinkMixturePoint d), MeasurableSet S →
        (∫⁻ z, ‖normalizedLinkMixtureAmplitude L γ δ Q J S z‖ₑ ∂productLinkMixtureMeasure d n J) ≤
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) * L ^ ((d : ℝ) * k)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_normalizedReplacedLinkMass_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan k J hJ S hS
  exact (lintegral_normalizedLinkMixtureAmplitude_le (hL₀.trans hL) hδ γ Q J hS).trans
    (hb L hL n Q hspan k J hJ)

end WaveTurbulence.Incoh
