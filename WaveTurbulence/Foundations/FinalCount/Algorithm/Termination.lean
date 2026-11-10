/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricStep
public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-! # Strict potential descent and linear run length

These results apply to the actual graph rewrite envelope. The separately
named progress helper does not replace source selector completeness.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

inductive Trace : State.{u,v} V → State.{u,v} V → ℕ → Prop
  | nil (s : State.{u,v} V) : Trace s s 0
  | cons {s t z : State.{u,v} V} {n : ℕ} : GeometricStep s t → Trace t z n → Trace s z (n+1)

theorem Trace.bond_budget {s t : State.{u,v} V} {n : ℕ} (h : Trace s t n) :
    t.bondPotential+n ≤ s.bondPotential := by
  induction h with
  | nil s => omega
  | cons hstep htrace ih =>
    have hh := hstep.bondPotential_lt
    omega

theorem State.bonds_le_two_mul_atoms (s : State.{u,v} V) (hM : s.graph.IsMolecule) :
    s.bondPotential ≤ 2*s.atomPotential := by
  have hs : ∑ v ∈ s.graph.atoms,s.graph.deg v ≤ ∑ _v ∈ s.graph.atoms,(4 : ℕ) :=
    Finset.sum_le_sum (fun v hv => deg_le_four s.graph hM hv)
  rw [sum_degrees_eq_two_mul_bonds] at hs
  simp only [Finset.sum_const,smul_eq_mul] at hs
  change s.graph.bonds.card ≤ 2*s.graph.atoms.card
  omega

end WaveTurbulence.Mole.AppbAlgorithm
