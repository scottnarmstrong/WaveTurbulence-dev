/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeClockFibers
public import WaveTurbulence.Foundations.Incoh.CausalBoxData
public import WaveTurbulence.Foundations.Incoh.LinkMixture

/-!
# Actual causal box parameters of a tree clock fiber

The frequency balance follows from complete paired selection. The
interval endpoints are those of the structural source fiber.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- Actual temporal frequencies and interval bounds, with no assumed phase balance. -/
@[expose] def TreeClockFibers.boxParameters {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (L γ δ : ℝ)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)))
    (u : Fin T.selection.coordinates.restCount → ℝ) : CausalBoxData m :=
  CausalBoxData.ofValues
    (T.selection.phase (fun i => linkTemporalFrequency L γ δ (Q i) (p i)))
    (T.lower u) (T.upper u) (T.selection.phase_sum _) (T.lower_le_upper u)

/-- The box parameters read the actual phase and remaining-clock coordinates of the mixture. -/
@[expose] def TreeClockFibers.mixtureParameters {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (L γ δ : ℝ) (z : Fin n → LinkMixturePoint d) : CausalBoxData m :=
  T.boxParameters L γ δ (fun i => (z i).1)
    (T.selection.coordinates.equiv (fun i => (z i).2)).2

/-- These literal parameters are measurable in the complete mixture variable. -/
theorem TreeClockFibers.measurable_mixtureParameters {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (L γ δ : ℝ) : Measurable (T.mixtureParameters L γ δ) := by
  have hu : Measurable (fun z : Fin n → LinkMixturePoint d =>
      (T.selection.coordinates.equiv (fun i => (z i).2)).2) := by
    apply measurable_snd.comp
    apply T.selection.coordinates.equiv.measurable.comp
    exact Measurable.of_eval (fun i => measurable_snd.comp (measurable_pi_apply i))
  have hp : Measurable (fun z : Fin n → LinkMixturePoint d =>
      T.selection.phase (fun i => linkTemporalFrequency L γ δ (Q i) (z i).1)) := by
    apply Measurable.of_eval
    intro a
    have hf : Measurable (linkTemporalFrequency L γ δ (Q (T.selection.pairing a).1.val)) :=
      measurable_of_countable _
    unfold SelectedLinkClocks.phase
    split_ifs
    · exact hf.comp (measurable_fst.comp (measurable_pi_apply _))
    · exact (hf.comp
        (measurable_fst.comp (measurable_pi_apply _))).neg
  exact (hp.prodMk ((T.measurable_lower.comp hu).prodMk (T.measurable_upper.comp hu))).subtype_mk

end WaveTurbulence.Incoh
