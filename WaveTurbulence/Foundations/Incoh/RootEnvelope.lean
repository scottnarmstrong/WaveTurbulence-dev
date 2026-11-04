/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.RootBoxes
public import WaveTurbulence.Foundations.Incoh.LinkAbsoluteBounds
public import WaveTurbulence.Foundations.Incoh.UnitBoxMarginal

/-!
# Removing only the root links

TARGET (incohproof18). Root links receive the proved trivial lattice
bound; all untouched links retain their actual oscillatory absolute values.
The resulting envelope factors over the unit root box.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The envelope retains every link factor except those touched by the two roots. -/
@[expose] def RootCoordinates.envelopeFactor {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (i : Fin n) (t : Fin 2 → ℝ) : ℝ≥0∞ :=
  if i ∈ R.rootLinks then ENNReal.ofReal ((5 * L) ^ (2 * d)) else ‖linkTimeFactor L γ δ (Q i) t‖ₑ

/-- The literal root-link envelope on the source product of layer boxes. -/
@[expose] def RootCoordinates.envelope {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (t : Fin n → Fin 2 → ℝ) : ℝ≥0∞ :=
  (univ.pi (fun i => linkBox (Q i))).indicator (fun t => ∏ i, R.envelopeFactor L γ δ Q i (t i)) t

/-- The lower endpoints provide a canonical point of the unit root box. -/
@[expose] def RootCoordinates.baseRootTimes {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) (a : Fin r) : ℝ := vertexLayer Q (R.rootVertex a)

theorem RootCoordinates.baseRootTimes_mem {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    (Q : Fin n → LayerLink d) : R.baseRootTimes Q ∈ R.rootBox Q := by
  constructor
  · intro a; exact le_rfl
  · intro a; change (vertexLayer Q (R.rootVertex a) : ℝ) ≤ (vertexLayer Q (R.rootVertex a) : ℝ) + 1; linarith

theorem RootCoordinates.measurable_envelope {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) :
    Measurable (R.envelope L γ δ Q) := by
  apply Measurable.indicator _ (MeasurableSet.univ_pi fun i => measurableSet_Icc)
  apply Finset.measurable_prod
  intro i _
  by_cases hi : i ∈ R.rootLinks
  · simp only [envelopeFactor, hi, ite_true]
    exact measurable_const
  · simp only [envelopeFactor, hi, ite_false]
    exact ((continuous_linkTimeFactor hL γ δ (Q i)).measurable.comp (measurable_pi_apply i)).enorm

/-- The envelope is exactly independent of the roots on their unit box. -/
theorem RootCoordinates.envelope_factorization {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (t : Fin r → ℝ) (u : Fin R.restCount → ℝ) :
    R.envelope L γ δ Q (R.equiv.symm (t, u)) =
      (R.rootBox Q).indicator (fun _ => R.envelope L γ δ Q (R.equiv.symm (R.baseRootTimes Q, u))) t := by
  by_cases ht : t ∈ R.rootBox Q
  · rw [Set.indicator_of_mem (s := R.rootBox Q) ht]
    by_cases hu : u ∈ R.restBox Q
    · have hB := (R.equiv_symm_mem_linkBoxes Q t u).mpr ⟨ht, hu⟩
      have hB₀ := (R.equiv_symm_mem_linkBoxes Q (R.baseRootTimes Q) u).mpr ⟨R.baseRootTimes_mem Q, hu⟩
      rw [envelope, envelope, Set.indicator_of_mem hB, Set.indicator_of_mem hB₀]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ R.rootLinks
      · simp only [envelopeFactor, hi, ite_true]
      · simp only [envelopeFactor, hi, ite_false]
        rw [R.equiv_symm_eq_of_notMem_rootLinks t (R.baseRootTimes Q) u i hi]
    · have hB : R.equiv.symm (t, u) ∉ univ.pi (fun i => linkBox (Q i)) := by
        intro h; exact hu ((R.equiv_symm_mem_linkBoxes Q t u).mp h).2
      have hB₀ : R.equiv.symm (R.baseRootTimes Q, u) ∉ univ.pi (fun i => linkBox (Q i)) := by
        intro h; exact hu ((R.equiv_symm_mem_linkBoxes Q (R.baseRootTimes Q) u).mp h).2
      rw [envelope, envelope, Set.indicator_of_notMem hB, Set.indicator_of_notMem hB₀]
  · have hB : R.equiv.symm (t, u) ∉ univ.pi (fun i => linkBox (Q i)) := by
      intro h; exact ht ((R.equiv_symm_mem_linkBoxes Q t u).mp h).1
    rw [envelope, Set.indicator_of_notMem hB, Set.indicator_of_notMem (s := R.rootBox Q) ht]

/-- Each root fiber of the literal envelope is bounded by its full absolute integral. -/
theorem RootCoordinates.lintegral_envelope_fiber_le {d n : ℕ} {r : ℕ} (R : RootCoordinates n r)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d) (t : Fin r → ℝ) :
    (∫⁻ u, R.envelope L γ δ Q (R.equiv.symm (t, u))) ≤ ∫⁻ v, R.envelope L γ δ Q v := by
  have hG := (R.measurable_envelope hL γ δ Q).comp R.equiv.symm.measurable
  have h := lintegral_fiber_le_of_unit_box_factorization measurableSet_Icc (R.volume_rootBox Q)
    hG (R.envelope_factorization L γ δ Q) t
  exact h.trans_eq (R.measurePreserving.symm.lintegral_comp_emb R.equiv.symm.measurableEmbedding
    (R.envelope L γ δ Q))

end WaveTurbulence.Incoh
