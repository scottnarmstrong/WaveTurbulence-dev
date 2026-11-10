/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.ComponentQuotient
public import WaveTurbulence.Foundations.FinalCount.Degen.BondDeletion
import Mathlib.Tactic

/-! # Actual circuit-rank changes for the corrected degenerate-atom split -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every new component has at least one crossing bond. -/
theorem card_newComponents_le_boundary (M : Molecule V D) (Y : Finset V) :
    (newComponents M Y).card ≤ (boundaryDarts M Y).card := by
  classical
  calc
    _ = ∑ _S ∈ newComponents M Y, 1 := by simp only [sum_const, smul_eq_mul, nsmul_eq_mul, mul_one]
    _ ≤ ∑ S ∈ newComponents M Y, (boundaryDarts M S).card := by
      apply sum_le_sum
      intro S hS
      exact card_pos.mpr (mem_filter.mp hS).2
    _ ≤ _ := sum_newComponents_boundary_card_le M Y

/-- F48's adopted criterion: if no residual component has exactly ONE
crossing BOND, every such component uses at least two boundary bonds. -/
theorem two_mul_card_newComponents_le_of_no_single (M : Molecule V D) (Y : Finset V)
    (hnosingle : ∀ S ∈ newComponents M Y, (boundaryDarts M S).card ≠ 1) :
    2 * (newComponents M Y).card ≤ (boundaryDarts M Y).card := by
  classical
  calc
    _ = ∑ _S ∈ newComponents M Y, 2 := by simp only [sum_const, smul_eq_mul, nsmul_eq_mul]; omega
    _ ≤ ∑ S ∈ newComponents M Y, (boundaryDarts M S).card := by
      apply sum_le_sum
      intro S hS
      have hp := card_pos.mpr (mem_filter.mp hS).2
      have hn := hnosingle S hS
      omega
    _ ≤ _ := sum_newComponents_boundary_card_le M Y

theorem card_atoms_erase_singleton_add_one (M : Molecule V D) {v : V} (hv : v ∈ M.atoms) :
    (eraseAtoms M {v}).atoms.card + 1 = M.atoms.card := by
  change (M.atoms \ {v}).card + 1 = _
  rw [sdiff_singleton_eq_erase]
  exact card_erase_add_one hv

end WaveTurbulence.Degen
