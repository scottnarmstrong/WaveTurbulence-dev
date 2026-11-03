/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.OrderChambers

/-!
# Permutation chambers and their volumes

Each strict coordinate-order chamber in `[0,D]^n` has volume `D^n/n!`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Analysis

/-- A strict coordinate-order chamber, with `σ` listing coordinates from
largest to smallest. -/
@[expose] def strictOrderChamber {n : ℕ} (D : ℝ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {x | (∀ i, x i ∈ Icc 0 D) ∧ StrictAnti (x ∘ σ)}

/-- Measurability of a strict order chamber. -/
theorem measurableSet_strictOrderChamber {n : ℕ} (D : ℝ) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (strictOrderChamber D σ) := by
  have hbounds : MeasurableSet {x : Fin n → ℝ | ∀ i, x i ∈ Icc 0 D} := by
    have heq : {x : Fin n → ℝ | ∀ i, x i ∈ Icc 0 D} =
        Set.pi univ (fun _ => Icc 0 D) := by ext x; simp only [mem_ofPred_eq, mem_pi, mem_univ, forall_const]
    rw [heq]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have ha : MeasurableSet {x : Fin n → ℝ | StrictAnti (x ∘ σ)} := by
    have heq : {x : Fin n → ℝ | StrictAnti (x ∘ σ)} =
        ⋂ i : Fin n, ⋂ j : Fin n, {x : Fin n → ℝ | i < j → x (σ j) < x (σ i)} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, StrictAnti, Function.comp_apply]
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i < j
    · simpa only [hij, true_implies] using
        measurableSet_lt (measurable_pi_apply (σ j)) (measurable_pi_apply (σ i))
    · simp only [hij, false_implies, ofPred_true, MeasurableSet.univ]
  exact hbounds.inter ha

/-- Different strict chambers are disjoint. -/
theorem disjoint_strictOrderChamber {n : ℕ} (D : ℝ) {σ τ : Equiv.Perm (Fin n)}
    (hστ : σ ≠ τ) : Disjoint (strictOrderChamber D σ) (strictOrderChamber D τ) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have he := Tuple.unique_antitone hx.2.antitone hy.2.antitone
  have hinj : Function.Injective x := by
    intro i j hij
    apply σ.symm.injective
    apply hx.2.injective
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij
  apply hστ
  apply Equiv.ext
  intro i
  exact hinj (congrFun he i)

/-- Every strict chamber has the same volume as the standard simplex.
Coordinate ties account for the difference between strict and weak orders. -/
theorem volume_strictOrderChamber {n : ℕ} {D : ℝ} (hD : 0 ≤ D) (σ : Equiv.Perm (Fin n)) :
    volume (strictOrderChamber D σ) = ENNReal.ofReal (D ^ n / (Nat.factorial n : ℝ)) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have he (x : Fin n → ℝ) : e x = x ∘ σ := by
    ext i
    simp only [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
      Equiv.symm_symm, Function.comp_apply, eq_rec_constant]
  have hae : strictOrderChamber D σ =ᵐ[volume] e ⁻¹' orderedSimplex n D := by
    filter_upwards [ae_injective_coordinates n] with x hx
    apply propext
    change ((∀ i, x i ∈ Icc 0 D) ∧ StrictAnti (x ∘ σ)) ↔ e x ∈ orderedSimplex n D
    rw [he, mem_orderedSimplex_iff]
    constructor
    · intro h
      exact ⟨fun i => h.1 (σ i), h.2.antitone⟩
    · rintro ⟨hb, ha⟩
      exact ⟨fun i => by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hb (σ.symm i),
        ha.strictAnti_of_injective (hx.comp σ.injective)⟩
  rw [measure_congr hae, hmp.measure_preimage (measurableSet_orderedSimplex n D).nullMeasurableSet,
    volume_orderedSimplex n hD]

end WaveTurbulence.Analysis
