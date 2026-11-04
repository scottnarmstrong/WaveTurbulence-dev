/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LinkMixtureMass
public import WaveTurbulence.Foundations.Incoh.NormalizedReplacementDecay

/-!
# Actual product phase/internal-clock mixtures

The product measure expands exactly the selected links. All other links
keep their oscillatory factors; source time-order constraints are imposed
by a measurable indicator.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Product of the literal selected/unselected link measures. -/
@[expose] def productLinkMixtureMeasure (d n : ℕ) (J : Finset (Fin n)) :
    Measure (Fin n → LinkMixturePoint d) :=
  Measure.pi (fun i => linkMixtureMeasure d (decide (i ∈ J)))

instance sigmaFinite_productLinkMixtureMeasure (d n : ℕ) (J : Finset (Fin n)) :
    SigmaFinite (productLinkMixtureMeasure d n J) := by
  unfold productLinkMixtureMeasure
  infer_instance

/-- The actual product amplitude before coupling normalization. -/
@[expose] def productLinkMixtureAmplitude {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (J : Finset (Fin n)) (S : Set (Fin n → LinkMixturePoint d)) (z : Fin n → LinkMixturePoint d) : ℂ :=
  S.indicator (fun z => ∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ J)) (z i)) z

/-- Measurability follows from the literal lattice and time factors. -/
theorem stronglyMeasurable_productLinkMixtureAmplitude {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    StronglyMeasurable (productLinkMixtureAmplitude L γ δ Q J S) := by
  apply StronglyMeasurable.indicator _ hS
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_prod
  intro i _
  exact (stronglyMeasurable_linkMixtureFactor hL γ δ (Q i) _).measurable.comp (measurable_pi_apply i)

/-- Integrability is proved from the literal factorization, with no mass hypothesis. -/
theorem integrable_productLinkMixtureAmplitude {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    Integrable (productLinkMixtureAmplitude L γ δ Q J S) (productLinkMixtureMeasure d n J) := by
  exact (Integrable.fintype_prod_dep
    (fun i => integrable_linkMixtureFactor hL γ δ (Q i) (decide (i ∈ J)))).indicator hS

/-- The mixture's absolute mass pays each selected replacement only once. -/
theorem lintegral_productLinkMixtureAmplitude_le {d n : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    (∫⁻ z, ‖productLinkMixtureAmplitude L γ δ Q J S z‖ₑ ∂productLinkMixtureMeasure d n J) ≤
      ∏ i, replacedLinkMass L γ δ Q J i := by
  unfold productLinkMixtureAmplitude productLinkMixtureMeasure
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator hS]
  have hf (i : Fin n) : IntegrableOn (linkMixtureFactor L γ δ (Q i) (decide (i ∈ J))) univ
      (linkMixtureMeasure d (decide (i ∈ J))) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      integrable_linkMixtureFactor (zero_lt_one.trans_le hL) γ δ (Q i) (decide (i ∈ J))
  apply (lintegral_pi_product_enorm_le (μ := fun i => linkMixtureMeasure d (decide (i ∈ J)))
    (B := fun _ => univ) (fun z _ => by simp) hf).trans
  apply Finset.prod_le_prod
  intro i _
  simpa only [Measure.restrict_univ] using lintegral_linkMixtureFactor_le hL γ δ Q J i

end WaveTurbulence.Incoh
