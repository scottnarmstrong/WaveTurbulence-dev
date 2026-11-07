/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ZeroLossDeletion
import Mathlib.Tactic

/-! # Exhaustive actual graph cases for DH23 10.1 operation(a) -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem low_degree_removal_cases (M : Molecule V D)
    (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x)) {v : V} (hv : v ∈ M.atoms)
    (hdeg : M.deg v ≤ 3) :
    (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank ∨
    (M.deg v = 2 ∧ (Degen.newComponents M {v}).card = 1 ∧
      (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank-1) ∨
    (M.deg v = 3 ∧ (Degen.newComponents M {v}).card = 2 ∧
      (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank-1) ∨
    (M.deg v = 3 ∧ (Degen.newComponents M {v}).card = 1 ∧
      (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank-2) := by
  classical
  have hdrop := circuitRank_erase_singleton_sub_general M hv
  rw [incidentBonds_card_eq_degree_of_loopless M hloop v] at hdrop
  have hC := Degen.card_newComponents_le_boundary M {v}
  have hb := Degen.card_boundary_add_twice_self_eq_deg M v
  have hCup : (Degen.newComponents M {v}).card ≤ M.deg v := by omega
  have hCpos : 0 < M.deg v → 0 < (Degen.newComponents M {v}).card := by
    intro hp
    obtain ⟨e,he⟩ := card_pos.mp hp
    have hev := (Mole.mem_dartsAt M v e).mp he
    obtain ⟨S,hS,_⟩ := incident_dart_residual_boundary M hloop hev
    exact card_pos.mpr ⟨S,hS⟩
  omega

end WaveTurbulence.MoleProp
