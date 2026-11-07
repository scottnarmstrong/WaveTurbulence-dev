/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentForest
import Mathlib.Tactic

/-! # Exact bond budget through actual forest edits, splits and discards -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

noncomputable def forestBonds (F : List (State.{u,v} V)) : ℕ :=
  (F.map State.bondPotential).sum

theorem forestBonds_split (s : State.{u,v} V) (S : Finset V) (hS : AppbClosedSide s.graph S) :
    forestBonds [ofMolecule (appbSideMolecule s.graph S hS),
      ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)] = s.bondPotential := by
  have hh := bonds_card_closed_side_add s.graph S hS
  simpa only [forestBonds,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,State.bondPotential,ofMolecule]
    using hh.symm

theorem ForestMove.bonds_le {F G : List (State.{u,v} V)} (h : ForestMove F G) :
    forestBonds G ≤ forestBonds F := by
  cases h with
  | @edit pre tail s t h =>
    have hh := h.bondPotential_lt
    simp only [forestBonds,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega
  | split pre tail s S hS hn hc =>
    have hh := forestBonds_split s S hS
    simp only [forestBonds,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at hh
    simp only [forestBonds,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega
  | discard pre tail s ht =>
    simp only [forestBonds,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega

theorem forestBonds_edit_decrease (pre tail : List (State.{u,v} V))
    {s t : State.{u,v} V} (h : GeometricStep s t) :
    forestBonds (pre++t::tail)+1 ≤ forestBonds (pre++s::tail) := by
  have hh := h.bondPotential_lt
  simp only [forestBonds,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
  omega

end WaveTurbulence.Mole.AppbAlgorithm
