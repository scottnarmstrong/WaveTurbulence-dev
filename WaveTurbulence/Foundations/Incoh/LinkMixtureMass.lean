/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LinkMixture
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Absolute mass of the literal link mixture

A selected link costs its phase coefficient mass exactly once. An
unselected link retains its actual oscillatory integral over the layer box.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Exact selected-link mass, before its uniform cutoff bound. -/
theorem lintegral_linkMixtureFactor_selected {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) :
    (∫⁻ z, ‖linkMixtureFactor L γ δ Q true z‖ₑ ∂linkMixtureMeasure d true) =
      ENNReal.ofReal (∑' p, ‖linkPhaseCoefficient L Q p‖) := by
  change (∫⁻ z : LinkMixturePoint d,
    ‖(linkBox Q).indicator (fun _ => linkPhaseCoefficient L Q z.1) z.2‖ₑ
      ∂(Measure.count.prod volume)) = _
  have hm := (stronglyMeasurable_linkMixtureFactor hL γ δ Q true).measurable.enorm
  change Measurable (fun z : LinkMixturePoint d =>
    ‖(linkBox Q).indicator (fun _ => linkPhaseCoefficient L Q z.1) z.2‖ₑ) at hm
  rw [lintegral_prod _ hm.aemeasurable]
  have he (p : (Fin d → ℤ) × (Fin d → ℤ)) :
      (∫⁻ t, ‖(linkBox Q).indicator (fun _ => linkPhaseCoefficient L Q p) t‖ₑ) =
        ‖linkPhaseCoefficient L Q p‖ₑ := by
    simp_rw [enorm_indicator_eq_indicator_enorm]
    rw [lintegral_indicator (s := linkBox Q) measurableSet_Icc, lintegral_const, Measure.restrict_apply_univ,
      volume_linkBox, mul_one]
  simp_rw [he]
  rw [lintegral_count]
  simp_rw [← ofReal_norm]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _)
    (summable_norm_linkTerm hL 0 Q.toLinkParameters)).symm

/-- Exact unselected-link mass. -/
theorem lintegral_linkMixtureFactor_unselected {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) :
    (∫⁻ z, ‖linkMixtureFactor L γ δ Q false z‖ₑ ∂linkMixtureMeasure d false) =
      layerLinkMass L (δ * L ^ (2 * γ)) Q := by
  change (∫⁻ z : LinkMixturePoint d, ‖(linkBox Q).indicator (linkTimeFactor L γ δ Q) z.2‖ₑ
    ∂((Measure.dirac 0).prod volume)) = _
  have hm := (stronglyMeasurable_linkMixtureFactor hL γ δ Q false).measurable.enorm
  change Measurable (fun z : LinkMixturePoint d => ‖(linkBox Q).indicator (linkTimeFactor L γ δ Q) z.2‖ₑ) at hm
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator (s := linkBox Q) measurableSet_Icc]
  simp only [lintegral_const, Measure.dirac_apply_of_mem (mem_univ _), mul_one]
  unfold layerLinkMass linkTimeFactor
  apply lintegral_congr
  intro t
  rw [show ((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1) =
    ((Q.orientation : ℤ) : ℝ) * (δ * L ^ (2 * γ)) * (t 0 - t 1) by ring]

/-- Every literal factor is bounded by the exact replacement mass used in product decay. -/
theorem lintegral_linkMixtureFactor_le {d n : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (J : Finset (Fin n)) (i : Fin n) :
    (∫⁻ z, ‖linkMixtureFactor L γ δ (Q i) (decide (i ∈ J)) z‖ₑ
      ∂linkMixtureMeasure d (decide (i ∈ J))) ≤ replacedLinkMass L γ δ Q J i := by
  classical
  by_cases hi : i ∈ J
  · simp only [hi, decide_true, replacedLinkMass, ite_true]
    rw [lintegral_linkMixtureFactor_selected (zero_lt_one.trans_le hL)]
    exact ENNReal.ofReal_le_ofReal (tsum_norm_linkPhaseCoefficient_le hL (Q i))
  · simp only [hi, decide_false, replacedLinkMass, ite_false]
    exact (lintegral_linkMixtureFactor_unselected (zero_lt_one.trans_le hL) γ δ (Q i)).le

end WaveTurbulence.Incoh
