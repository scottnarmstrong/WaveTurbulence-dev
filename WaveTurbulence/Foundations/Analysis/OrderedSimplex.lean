/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Volumes of ordered simplices

The monotone-chain domains used at TARGET L2029–2036. Coordinates are ordered
from the largest to the smallest, and endpoints are included; boundaries
have zero Lebesgue measure.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Analysis

/-- The region `0 ≤ tₙ ≤ ⋯ ≤ t₁ ≤ D`, with coordinates numbered from zero.
The zero-dimensional region is the singleton coordinate space. -/
@[expose] def orderedSimplex : (n : ℕ) → ℝ → Set (Fin n → ℝ)
  | 0, _ => Set.univ
  | n + 1, D => {x | x 0 ∈ Icc 0 D ∧ Fin.tail x ∈ orderedSimplex n (x 0)}

/-- Joint measurability in the upper endpoint and all simplex coordinates. -/
theorem measurableSet_orderedSimplex_total : ∀ n : ℕ,
    MeasurableSet {p : ℝ × (Fin n → ℝ) | p.2 ∈ orderedSimplex n p.1} := by
  intro n
  induction n with
  | zero => simpa only [orderedSimplex, mem_univ, ofPred_true] using MeasurableSet.univ
  | succ n ih =>
      have hm : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) => (p.2 0, Fin.tail p.2)) := by
        fun_prop
      have h0 : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) => p.2 0) := by fun_prop
      have heq : {p : ℝ × (Fin (n + 1) → ℝ) | p.2 ∈ orderedSimplex (n + 1) p.1} =
          {p | 0 ≤ p.2 0} ∩ {p | p.2 0 ≤ p.1} ∩
            ((fun p => (p.2 0, Fin.tail p.2)) ⁻¹'
              {p : ℝ × (Fin n → ℝ) | p.2 ∈ orderedSimplex n p.1}) := by
        ext p
        simp only [orderedSimplex, mem_ofPred_eq, mem_Icc, mem_inter_iff, mem_preimage,
          and_assoc]
      rw [heq]
      exact ((measurableSet_le measurable_const h0).inter
        (measurableSet_le h0 measurable_fst)).inter (ih.preimage hm)

theorem measurableSet_orderedSimplex (n : ℕ) (D : ℝ) :
    MeasurableSet (orderedSimplex n D) :=
  (measurableSet_orderedSimplex_total n).preimage (measurable_const.prodMk measurable_id)

/-- Fubini recursion for the volume of an ordered simplex. -/
theorem volume_orderedSimplex_succ (n : ℕ) (D : ℝ) :
    volume (orderedSimplex (n + 1) D) =
      ∫⁻ t in Icc (0 : ℝ) D, volume (orderedSimplex n t) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hs := measurableSet_orderedSimplex (n + 1) D
  have heq : e.symm ⁻¹' orderedSimplex (n + 1) D =
      {p : ℝ × (Fin n → ℝ) | p.1 ∈ Icc 0 D ∧ p.2 ∈ orderedSimplex n p.1} := by
    ext p
    simp only [mem_preimage, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv_zero, Fin.consEquiv, Equiv.coe_fn_mk, orderedSimplex,
      Fin.cons_zero, Fin.tail_cons, mem_ofPred_eq]
  have hm : MeasurableSet (e.symm ⁻¹' orderedSimplex (n + 1) D) := hs.preimage e.symm.measurable
  rw [← hmp.measure_preimage hs.nullMeasurableSet]
  change (volume.prod volume) (e.symm ⁻¹' orderedSimplex (n + 1) D) = _
  rw [Measure.prod_apply hm]
  rw [heq]
  have hfun : (fun t : ℝ => volume (Prod.mk t ⁻¹'
      {p : ℝ × (Fin n → ℝ) | p.1 ∈ Icc 0 D ∧ p.2 ∈ orderedSimplex n p.1})) =
      (Icc (0 : ℝ) D).indicator (fun t => volume (orderedSimplex n t)) := by
    funext t
    by_cases ht : t ∈ Icc 0 D
    · simp only [preimage_ofPred_eq, ht, true_and, indicator_of_mem ht, ofPred_mem_eq]
    · simp only [preimage_ofPred_eq, ht, false_and, ofPred_false, measure_empty,
        indicator_of_notMem ht]
  rw [hfun, lintegral_indicator measurableSet_Icc]

end WaveTurbulence.Analysis
