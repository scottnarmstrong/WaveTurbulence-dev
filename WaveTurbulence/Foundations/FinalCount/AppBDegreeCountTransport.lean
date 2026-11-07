/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
import Mathlib.Tactic

/-! # Local changes of actual degree statistics on a fixed atom set -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [Fintype E]

/-- The degree-count change is supported exactly on the changed vertices.
This general finite-sum identity is independent of any operation. -/
theorem appb_degreeCount_difference_of_local_change (M : Molecule V D) (N : Molecule V E)
    (hatoms : N.atoms = M.atoms) (S : Finset V) (hS : S ⊆ M.atoms)
    (hdeg : ∀ v ∈ M.atoms, v ∉ S → N.deg v = M.deg v) (j : ℕ) :
    ((appbDegreeAtoms N j).card : ℤ) - (appbDegreeAtoms M j).card =
      ∑ v ∈ S, ((if N.deg v = j then (1 : ℤ) else 0) - (if M.deg v = j then 1 else 0)) := by
  classical
  have hp : ((appbDegreeAtoms N j).card : ℤ) =
      ∑ v ∈ M.atoms, if N.deg v = j then (1 : ℤ) else 0 := by
    change ((N.atoms.filter fun v => N.deg v = j).card : ℤ) = _
    rw [hatoms,sum_boole]
  have hm : ((appbDegreeAtoms M j).card : ℤ) =
      ∑ v ∈ M.atoms, if M.deg v = j then (1 : ℤ) else 0 := (sum_boole _ _).symm
  rw [hp,hm,← sum_sub_distrib]
  symm
  apply sum_subset hS
  intro v hv hout
  simp only [hdeg v hv hout,sub_self]

end WaveTurbulence.Mole
