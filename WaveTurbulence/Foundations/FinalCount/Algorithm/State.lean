/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
import Mathlib.Tactic

/-! # A current molecule with its changing finite dart carrier

The algorithm deletes darts and sometimes adjoins a new pair. The state
therefore carries the actual finite dart type, not an abstract list of
graph statistics or operation conclusions.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v

structure State (V : Type v) where
  Dart : Type u
  dartFintype : Fintype Dart
  dartDecidableEq : DecidableEq Dart
  graph : Molecule V Dart

attribute [instance] State.dartFintype State.dartDecidableEq

variable {V : Type v} [DecidableEq V]

def ofMolecule {D : Type u} [Fintype D] [DecidableEq D] (M : Molecule V D) : State.{u,v} V :=
  ⟨D,inferInstance,inferInstance,M⟩

noncomputable def State.bondPotential (s : State.{u,v} V) : ℕ := s.graph.bonds.card

noncomputable def State.atomPotential (s : State.{u,v} V) : ℕ := s.graph.atoms.card

end WaveTurbulence.Mole.AppbAlgorithm
