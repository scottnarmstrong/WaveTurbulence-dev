/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentForest
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentBalancedPotential
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedTrace
import Mathlib.Tactic

/-! # Resource accounting through actual component splitting

This is a conditional endpoint for a constructed source run. It neither
constructs that run nor identifies the controlled events with good/fine
operations. All increments are derived from literal graph constructors.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

noncomputable def forestBalancedPotential (F : List (State.{u,v} V)) : ℤ :=
  (F.map fun s => balancedPotential s.graph).sum

inductive BalancedForestStep : List (State.{u,v} V) → List (State.{u,v} V) → ℕ → ℕ → Prop
  | edit (pre tail : List (State.{u,v} V)) {s t : State.{u,v} V} {n c : ℕ}
      (h : BalancedStep s t n c) : BalancedForestStep (pre++s::tail) (pre++t::tail) n c
  | split (pre tail : List (State.{u,v} V)) (s : State.{u,v} V)
      (S : Finset V) (hS : AppbClosedSide s.graph S)
      (hn : S.Nonempty) (hc : (s.graph.atoms \ S).Nonempty) :
      BalancedForestStep (pre++s::tail)
        (pre++ofMolecule (appbSideMolecule s.graph S hS)::
          ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)::tail) 0 0
  | discard (pre tail : List (State.{u,v} V)) (s : State.{u,v} V) (ht : Terminal s) :
      BalancedForestStep (pre++s::tail) (pre++tail) 0 0

theorem BalancedForestStep.potential_bound {F G : List (State.{u,v} V)} {n c : ℕ}
    (h : BalancedForestStep F G n c) :
    forestBalancedPotential F+2*(n : ℤ)-16000*(c : ℤ) ≤ forestBalancedPotential G := by
  cases h with
  | edit pre tail h =>
    have hh := h.potential_bound
    simp only [forestBalancedPotential,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega
  | split pre tail s S hS hn hc =>
    have hh := balancedPotential_closed_side_add s.graph S hS
    simp only [forestBalancedPotential,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    change (pre.map (fun q => balancedPotential q.graph)).sum+(balancedPotential s.graph+(tail.map (fun q => balancedPotential q.graph)).sum) + 2*(0 : ℤ)-16000*(0 : ℤ) ≤
      (pre.map (fun q => balancedPotential q.graph)).sum+(balancedPotential (appbSideMolecule s.graph S hS)+(balancedPotential (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)+(tail.map (fun q => balancedPotential q.graph)).sum))
    rw [hh]
    omega
  | discard pre tail s ht =>
    have hh := balancedPotential_zero_terminal s.graph ht
    simp only [forestBalancedPotential,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega

theorem BalancedForestStep.forestMove {F G : List (State.{u,v} V)} {n c : ℕ}
    (h : BalancedForestStep F G n c) : ForestMove F G := by
  cases h with
  | edit pre tail h => exact .edit pre tail h.geometric
  | split pre tail s S hS hn hc => exact .split pre tail s S hS hn hc
  | discard pre tail s ht => exact .discard pre tail s ht

inductive BalancedForestTrace : List (State.{u,v} V) → List (State.{u,v} V) → ℕ → ℕ → Prop
  | nil (F : List (State.{u,v} V)) : BalancedForestTrace F F 0 0
  | cons {F G H : List (State.{u,v} V)} {n c m d : ℕ} :
      BalancedForestStep F G n c → BalancedForestTrace G H m d → BalancedForestTrace F H (n+m) (c+d)

theorem BalancedForestTrace.potential_bound {F G : List (State.{u,v} V)} {n c : ℕ}
    (h : BalancedForestTrace F G n c) :
    forestBalancedPotential F+2*(n : ℤ)-16000*(c : ℤ) ≤ forestBalancedPotential G := by
  induction h with
  | nil F => simp
  | cons hstep htrace ih =>
    have hh := hstep.potential_bound
    push_cast
    omega

/-- Component splitting has zero resource cost. Thus the same constant
8000 applies to a constructed run that processes components separately. -/
theorem normal_count_le_controlled_forest_trace (s : State.{u,v} V) {n c : ℕ}
    (hM : s.graph.IsMolecule) (hnu : appbNu s.graph ≤ 0)
    (h : BalancedForestTrace [s] [] n c) : n ≤ 8000*c := by
  have hi := balancedPotential_nonneg_initial s.graph hM hnu
  have hh := h.potential_bound
  simp only [forestBalancedPotential,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at hh
  omega

end WaveTurbulence.Mole.AppbAlgorithm
