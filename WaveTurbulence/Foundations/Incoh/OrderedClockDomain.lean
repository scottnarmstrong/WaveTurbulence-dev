/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Literal ordered clock domains

The domain records all clock bounds and the descendant ordering. Its
head/tail decomposition is purely structural and contains no estimates.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The closed ordered simplex `t ≥ v₀ ≥ ⋯ ≥ vₙ₋₁ ≥ s`. -/
@[expose] def orderedClockDomain (n : ℕ) (t s : ℝ) : Set (Fin n → ℝ) :=
  {v | (∀ i, s ≤ v i ∧ v i ≤ t) ∧ Antitone v}

/-- Ordered clock constraints remain measurable with measurable endpoints and coordinates. -/
theorem measurableSet_orderedClockDomain_comp {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    {t s : Z → ℝ} {v : Z → Fin n → ℝ} (ht : Measurable t) (hs : Measurable s) (hv : Measurable v) :
    MeasurableSet {z | v z ∈ orderedClockDomain n (t z) (s z)} := by
  have hbox : MeasurableSet (⋂ i : Fin n, {z | s z ≤ v z i ∧ v z i ≤ t z}) := by
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_le hs ((measurable_pi_apply i).comp hv)).inter
      (measurableSet_le ((measurable_pi_apply i).comp hv) ht)
  have hord : MeasurableSet (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_h : i ≤ j), {z | v z j ≤ v z i}) := by
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le ((measurable_pi_apply j).comp hv) ((measurable_pi_apply i).comp hv)
  have he : {z | v z ∈ orderedClockDomain n (t z) (s z)} =
      (⋂ i : Fin n, {z | s z ≤ v z i ∧ v z i ≤ t z}) ∩
        (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_h : i ≤ j), {z | v z j ≤ v z i}) := by
    ext z
    simp only [orderedClockDomain, Antitone, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [he]
  exact hbox.inter hord

theorem measurableSet_orderedClockDomain (n : ℕ) (t s : ℝ) :
    MeasurableSet (orderedClockDomain n t s) :=
  measurableSet_orderedClockDomain_comp measurable_const measurable_const measurable_id

theorem orderedClockDomain_subset_box (n : ℕ) (t s : ℝ) :
    orderedClockDomain n t s ⊆ Icc (fun _ => s) (fun _ => t) := by
  intro v hv
  exact ⟨fun i => (hv.1 i).1, fun i => (hv.1 i).2⟩

/-- Splitting off the root clock yields the exact lower-dimensional ordered domain. -/
theorem cons_mem_orderedClockDomain_iff {n : ℕ} (x : ℝ) (v : Fin n → ℝ) (t s : ℝ) :
    Fin.cons x v ∈ orderedClockDomain (n + 1) t s ↔
      x ∈ Icc s t ∧ v ∈ orderedClockDomain n x s := by
  constructor
  · intro h
    refine ⟨h.1 0, ⟨?_, ?_⟩⟩
    · intro i
      exact ⟨(h.1 i.succ).1, by
        simpa only [Fin.cons_zero, Fin.cons_succ] using h.2 (Fin.zero_le i.succ)⟩
    · intro i j hij
      exact h.2 (Fin.succ_le_succ_iff.mpr hij)
  · rintro ⟨hx, hv⟩
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hx
      · exact ⟨(hv.1 j).1, (hv.1 j).2.trans hx.2⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact le_rfl
        | succ j => exact (hv.1 j).2
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_zero] at hij
          omega
        | succ j => exact hv.2 (Fin.succ_le_succ_iff.mp hij)

/-- Bounded measurable functions are integrable on the literal finite clock simplex. -/
theorem integrableOn_orderedClockDomain {n : ℕ} {F : (Fin n → ℝ) → ℂ}
    (hF : StronglyMeasurable F) {C : ℝ} (hb : ∀ v, ‖F v‖ ≤ C) (t s : ℝ) :
    IntegrableOn F (orderedClockDomain n t s) := by
  let B : Set (Fin n → ℝ) := Icc (fun _ => s) (fun _ => t)
  let : IsFiniteMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hi : IntegrableOn F B := (integrable_const C).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  exact hi.mono_set (orderedClockDomain_subset_box n t s)

end WaveTurbulence.Incoh
