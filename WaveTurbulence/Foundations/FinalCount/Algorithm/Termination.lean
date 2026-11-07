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

theorem geometricStep_wellFounded : WellFounded (fun t s : State.{u,v} V => GeometricStep s t) :=
  Subrelation.wf (fun {_ _} h => GeometricStep.bondPotential_lt h) (InvImage.wf State.bondPotential Nat.lt_wfRel.wf)

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

theorem Trace.length_le_bonds {s t : State.{u,v} V} {n : ℕ} (h : Trace s t n) :
    n ≤ s.bondPotential := by
  have hh := h.bond_budget
  omega

theorem State.bonds_le_two_mul_atoms (s : State.{u,v} V) (hM : s.graph.IsMolecule) :
    s.bondPotential ≤ 2*s.atomPotential := by
  have hs : ∑ v ∈ s.graph.atoms,s.graph.deg v ≤ ∑ _v ∈ s.graph.atoms,(4 : ℕ) :=
    Finset.sum_le_sum (fun v hv => deg_le_four s.graph hM hv)
  rw [sum_degrees_eq_two_mul_bonds] at hs
  simp only [Finset.sum_const,smul_eq_mul] at hs
  change s.graph.bonds.card ≤ 2*s.graph.atoms.card
  omega

theorem Trace.length_le_two_mul_atoms {s t : State.{u,v} V} {n : ℕ}
    (h : Trace s t n) (hM : s.graph.IsMolecule) : n ≤ 2*s.atomPotential :=
  h.length_le_bonds.trans (s.bonds_le_two_mul_atoms hM)

theorem no_infinite_geometric_run :
    ¬∃ f : ℕ → State.{u,v} V,∀ n,GeometricStep (f n) (f (n+1)) := by
  rintro ⟨f,hf⟩
  have hb : ∀ n,(f n).bondPotential+n ≤ (f 0).bondPotential := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have hh := (hf n).bondPotential_lt
      omega
  have hh := hb ((f 0).bondPotential+1)
  omega

/-- Conditional termination helper for a proved selector-progress result.
The source algorithm must separately provide its priority-complete selector. -/
theorem exists_terminal_trace_of_progress (Terminal : State.{u,v} V → Prop)
    (hprogress : ∀ s,¬Terminal s → ∃ t,GeometricStep s t) (s : State.{u,v} V) :
    ∃ t n,Trace s t n ∧ Terminal t ∧ n ≤ s.bondPotential := by
  classical
  refine (geometricStep_wellFounded (V := V)).induction
    (C := fun s : State.{u,v} V => ∃ t n,Trace s t n ∧ Terminal t ∧ n ≤ s.bondPotential) s ?_
  intro s ih
  by_cases hs : Terminal s
  · exact ⟨s,0,.nil s,hs,Nat.zero_le _⟩
  · obtain ⟨t,ht⟩ := hprogress s hs
    obtain ⟨z,n,htrace,hz,hbound⟩ := ih t ht
    have hrun := Trace.cons ht htrace
    exact ⟨z,n+1,hrun,hz,hrun.length_le_bonds⟩

end WaveTurbulence.Mole.AppbAlgorithm
