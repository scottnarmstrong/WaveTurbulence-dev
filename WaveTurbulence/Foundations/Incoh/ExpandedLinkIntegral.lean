/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.ExpandedLinkFactor

/-!
# Exact selected-link phase representation of the source time integral

This identity uses the literal lattice sums and arbitrary measurable
source time domains contained in the product layer box.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Integrate all selected lattice phases while keeping the vertex clocks fixed. -/
theorem integral_expandedLinkArray {d n : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (J : Finset (Fin n)) (t : Fin n → Fin 2 → ℝ) :
    (∫ p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)),
      ∏ i, (linkMixtureFactor L γ δ (Q i) (decide (i ∈ J)) (p i, t i) *
        linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (p i, t i))
      ∂Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ J)))) =
      ∏ i, (linkBox (Q i)).indicator (linkTimeFactor L γ δ (Q i)) (t i) := by
  classical
  rw [integral_fintype_prod_eq_prod (f := fun i p =>
    linkMixtureFactor L γ δ (Q i) (decide (i ∈ J)) (p, t i) *
      linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (p, t i))]
  exact Finset.prod_congr rfl (fun i _ => integral_expandedLinkFactor hL γ δ (Q i) _ (t i))

/-- TARGET (incohproof21): the literal product integral equals its selected-phase mixture. -/
theorem integral_source_eq_expandedMixture {d n : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (J : Finset (Fin n))
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I)
    (hbox : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    (∫ t in I, ∏ i, linkTimeFactor L γ δ (Q i) (t i)) =
      ∫ z, productLinkMixtureAmplitude L γ δ Q J
          ((fun z i => (z i).2) ⁻¹' I) z *
        ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (z i)
        ∂productLinkMixtureMeasure d n J := by
  classical
  have ht : Measurable (fun z : Fin n → LinkMixturePoint d => fun i => (z i).2) :=
    Measurable.of_eval (fun i => measurable_snd.comp (measurable_pi_apply i))
  rw [integral_phaseTimeSplit J _ (integrable_expandedLinkMixture hL γ δ Q J (hI.preimage ht)),
    ← integral_indicator hI]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hi : t ∈ I
  · have hib : ∀ i, t i ∈ linkBox (Q i) := fun i => hbox hi i (mem_univ i)
    simp only [productLinkMixtureAmplitude, mem_preimage, hi, indicator_of_mem]
    simp_rw [← Finset.prod_mul_distrib]
    rw [integral_expandedLinkArray hL γ δ Q J t]
    exact Finset.prod_congr rfl (fun i _ => (indicator_of_mem (hib i) _).symm)
  · simp [productLinkMixtureAmplitude, hi]

end WaveTurbulence.Incoh
