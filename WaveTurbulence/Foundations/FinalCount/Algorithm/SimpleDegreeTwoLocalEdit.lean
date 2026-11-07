/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwo
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeThreeChangeBound
import Mathlib.Tactic

/-! # Local V2-star change on a fixed atom set -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [Fintype E]

open Classical in
/-- A conditional local-edit identity. Graph-specific producers must
prove the predicate transport away from the edited endpoints. -/
theorem simpleDegreeTwo_difference_of_local_edit (M : Molecule V D) (N : Molecule V E)
    (hatoms : N.atoms = M.atoms) (S : Finset V) (hS : S ⊆ M.atoms)
    (hout : ∀ v ∈ M.atoms,v ∉ S → (SimpleDegreeTwo N v ↔ SimpleDegreeTwo M v)) :
    ((simpleDegreeTwoAtoms N).card : ℤ)-(simpleDegreeTwoAtoms M).card =
      ∑ v ∈ S,((if SimpleDegreeTwo N v then (1 : ℤ) else 0)-
        (if SimpleDegreeTwo M v then 1 else 0)) := by
  classical
  have hN : ((simpleDegreeTwoAtoms N).card : ℤ) =
      ∑ v ∈ M.atoms,if SimpleDegreeTwo N v then (1 : ℤ) else 0 := by
    unfold simpleDegreeTwoAtoms
    rw [hatoms,sum_boole]
  have hM : ((simpleDegreeTwoAtoms M).card : ℤ) =
      ∑ v ∈ M.atoms,if SimpleDegreeTwo M v then (1 : ℤ) else 0 := by
    unfold simpleDegreeTwoAtoms
    rw [sum_boole]
  rw [hN,hM,← sum_sub_distrib]
  symm
  apply sum_subset hS
  intro v hv hn
  simp only [hout v hv hn,sub_self]

theorem simpleDegreeTwo_local_edit_abs_le (M : Molecule V D) (N : Molecule V E)
    (hatoms : N.atoms = M.atoms) (S : Finset V) (hS : S ⊆ M.atoms)
    (hout : ∀ v ∈ M.atoms,v ∉ S → (SimpleDegreeTwo N v ↔ SimpleDegreeTwo M v)) :
    |((simpleDegreeTwoAtoms N).card : ℤ)-(simpleDegreeTwoAtoms M).card| ≤ S.card := by
  classical
  rw [simpleDegreeTwo_difference_of_local_edit M N hatoms S hS hout]
  exact sum_indicator_difference_abs_le S _ _

end WaveTurbulence.Mole.AppbAlgorithm
