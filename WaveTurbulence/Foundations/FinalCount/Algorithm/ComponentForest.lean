/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricMass
public import WaveTurbulence.Foundations.FinalCount.Algorithm.Terminal
import Mathlib.Tactic

/-! # Termination with explicit component splitting

Graph edits, splitting a proper closed side and discarding a terminal
component all strictly lower one finite forest measure. No scheduler
progress premise or operation count inequality is stored in a move.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

noncomputable def forestWeight (F : List (State.{u,v} V)) : ℕ :=
  (F.map fun s => s.mass^2+1).sum

inductive ForestMove : List (State.{u,v} V) → List (State.{u,v} V) → Prop
  | edit (pre tail : List (State.{u,v} V)) {s t : State.{u,v} V} (h : GeometricStep s t) :
      ForestMove (pre++s::tail) (pre++t::tail)
  | split (pre tail : List (State.{u,v} V)) (s : State.{u,v} V)
      (S : Finset V) (hS : AppbClosedSide s.graph S)
      (hn : S.Nonempty) (hc : (s.graph.atoms \ S).Nonempty) :
      ForestMove (pre++s::tail)
        (pre++ofMolecule (appbSideMolecule s.graph S hS)::
          ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)::tail)
  | discard (pre tail : List (State.{u,v} V)) (s : State.{u,v} V) (ht : Terminal s) :
      ForestMove (pre++s::tail) (pre++tail)

theorem ForestMove.weight_lt {F G : List (State.{u,v} V)} (h : ForestMove F G) :
    forestWeight G < forestWeight F := by
  cases h with
  | @edit pre tail s t h =>
    have hm := h.mass_lt
    have hs : t.mass^2+1 < s.mass^2+1 := by
      nlinarith only [hm,Nat.zero_le t.mass,Nat.zero_le s.mass]
    simp only [forestWeight,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega
  | split pre tail s S hS hn hc =>
    let a := ofMolecule (appbSideMolecule s.graph S hS)
    let b := ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)
    have ha : 0 < a.mass := by
      have hh := Finset.card_pos.mpr hn
      change 0 < (appbSideMolecule s.graph S hS).bonds.card+S.card
      omega
    have hb : 0 < b.mass := by
      have hh := Finset.card_pos.mpr hc
      change 0 < (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement).bonds.card+
        (s.graph.atoms \ S).card
      omega
    have hm : s.mass = a.mass+b.mass := mass_closed_side_add s S hS
    have hab : 0 < a.mass*b.mass := Nat.mul_pos ha hb
    have hlocal : a.mass^2+1+(b.mass^2+1) < s.mass^2+1 := by nlinarith only [hm,hab]
    change forestWeight (pre++a::b::tail) < _
    simp only [forestWeight,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega
  | discard pre tail s ht =>
    simp only [forestWeight,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega

theorem forestMove_wellFounded :
    WellFounded (fun G F : List (State.{u,v} V) => ForestMove F G) :=
  Subrelation.wf (fun {_ _} h => h.weight_lt) (InvImage.wf forestWeight Nat.lt_wfRel.wf)

end WaveTurbulence.Mole.AppbAlgorithm
