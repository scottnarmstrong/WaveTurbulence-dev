/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeCountChange
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeThreeChangeBound
import Mathlib.Tactic

/-! # Uniform bounded changes of every degree count, including isolated atoms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E]

theorem deletion_degreeCount_change_abs_le {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (k : ℕ) :
    |((appbDegreeAtoms r.post k).card : ℤ)-(appbDegreeAtoms M k).card| ≤ P.vertices.card := by
  classical
  rw [TableDegree.post_degreeCount_difference r k]
  exact sum_indicator_difference_abs_le P.vertices
    (fun a => a ∉ P.removed ∧ M.deg (r.vertex a) = k+P.localDegree a)
    (fun a => M.deg (r.vertex a) = k)

theorem same_atoms_degreeCount_change_abs_le (M : Molecule V D) (N : Molecule V E)
    (hatoms : N.atoms = M.atoms) (S : Finset V) (hS : S ⊆ M.atoms)
    (hdeg : ∀ v ∈ M.atoms,v ∉ S → N.deg v = M.deg v) (k : ℕ) :
    |((appbDegreeAtoms N k).card : ℤ)-(appbDegreeAtoms M k).card| ≤ S.card := by
  classical
  rw [appb_degreeCount_difference_of_local_change M N hatoms S hS hdeg k]
  exact sum_indicator_difference_abs_le S (fun v => N.deg v = k) (fun v => M.deg v = k)

end WaveTurbulence.Mole.AppbAlgorithm
