/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SelectedLinkClocks
public import WaveTurbulence.Foundations.Incoh.RootBoxes

/-!
# Structural rectangular fibers of the selected tree clocks

The remaining clocks impose interval constraints on the selected clocks.
The source domain below adds their descendant ordering. No analytic
estimate is a field of this carrier.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The finite clock and time-domain data needed for TARGET (incohproof22)–(23). -/
structure TreeClockFibers {d n : ℕ} (m : ℕ) (Q : Fin n → LayerLink d) where
  selection : SelectedLinkClocks n (m + 2)
  remainingDomain : Set (Fin selection.coordinates.restCount → ℝ)
  measurable_remainingDomain : MeasurableSet remainingDomain
  lower : (Fin selection.coordinates.restCount → ℝ) → Fin (m + 2) → ℝ
  upper : (Fin selection.coordinates.restCount → ℝ) → Fin (m + 2) → ℝ
  measurable_lower : Measurable lower
  measurable_upper : Measurable upper
  lower_le_upper : ∀ u, lower u ≤ upper u
  remaining_mem_box : remainingDomain ⊆ selection.coordinates.restBox Q
  interval_mem_box : ∀ u ∈ remainingDomain, ∀ v,
    (∀ j, lower u j < v j ∧ v j ≤ upper u j) → v ∈ selection.coordinates.rootBox Q

/-- The actual source time domain, in the original vertex coordinates. -/
@[expose] def TreeClockFibers.timeDomain {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) : Set (Fin n → Fin 2 → ℝ) :=
  {t | let z := T.selection.coordinates.equiv t
       z.2 ∈ T.remainingDomain ∧
       (∀ j, T.lower z.2 j < z.1 j ∧ z.1 j ≤ T.upper z.2 j) ∧
       (∀ j : Fin (m + 1), z.1 j.succ < z.1 j.castSucc)}

/-- All fiber constraints are measurable in the literal vertex coordinates. -/
theorem TreeClockFibers.measurableSet_timeDomain {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) : MeasurableSet T.timeDomain := by
  have he := T.selection.coordinates.equiv.measurable
  have hv (j : Fin (m + 2)) : Measurable (fun t => (T.selection.coordinates.equiv t).1 j) :=
    (measurable_pi_apply j).comp (measurable_fst.comp he)
  have hl (j : Fin (m + 2)) : Measurable (fun t => T.lower (T.selection.coordinates.equiv t).2 j) :=
    (measurable_pi_apply j).comp (T.measurable_lower.comp (measurable_snd.comp he))
  have hu (j : Fin (m + 2)) : Measurable (fun t => T.upper (T.selection.coordinates.equiv t).2 j) :=
    (measurable_pi_apply j).comp (T.measurable_upper.comp (measurable_snd.comp he))
  have hb : MeasurableSet {t | ∀ j, T.lower (T.selection.coordinates.equiv t).2 j <
      (T.selection.coordinates.equiv t).1 j ∧ (T.selection.coordinates.equiv t).1 j ≤
        T.upper (T.selection.coordinates.equiv t).2 j} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun j => (measurableSet_lt (hl j) (hv j)).inter
      (measurableSet_le (hv j) (hu j))
  have ho : MeasurableSet {t | ∀ j : Fin (m + 1),
      (T.selection.coordinates.equiv t).1 j.succ < (T.selection.coordinates.equiv t).1 j.castSucc} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_lt (hv j.succ) (hv j.castSucc)
  exact (T.measurable_remainingDomain.preimage (measurable_snd.comp he)).inter (hb.inter ho)

/-- The original product layer box is a proved containment, rather than a norm premise. -/
theorem TreeClockFibers.timeDomain_subset_linkBoxes {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) : T.timeDomain ⊆ univ.pi (fun i => linkBox (Q i)) := by
  intro t ht
  obtain ⟨hu, hv, _⟩ := ht
  have h := (T.selection.coordinates.equiv_symm_mem_linkBoxes Q
    (T.selection.coordinates.equiv t).1 (T.selection.coordinates.equiv t).2).mpr
      ⟨T.interval_mem_box _ hu _ hv, T.remaining_mem_box hu⟩
  simpa only [Prod.eta, MeasurableEquiv.symm_apply_apply] using h

end WaveTurbulence.Incoh
