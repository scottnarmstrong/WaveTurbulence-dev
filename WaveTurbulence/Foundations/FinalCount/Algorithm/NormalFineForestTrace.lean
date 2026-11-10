/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalFineTrace
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentBalancedPotential
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentForest
import Mathlib.Tactic

/-! # The good-free contradiction survives processing components separately

This is a conditional run endpoint, not a construction of the source
algorithm. Normal/fine edits are literal graph operations; component
splitting has exactly zero defect-resource cost.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

noncomputable def forestDefectPotential (F : List (State.{u,v} V)) : ℤ :=
  (F.map fun s => defectPotential s.graph).sum

inductive NormalFineForestStep : List (State.{u,v} V) → List (State.{u,v} V) → Prop
  | edit (pre tail : List (State.{u,v} V)) {s t : State.{u,v} V}
      (h : NormalFineStep s t) (hM : s.graph.IsMolecule) :
      NormalFineForestStep (pre++s::tail) (pre++t::tail)
  | split (pre tail : List (State.{u,v} V)) (s : State.{u,v} V)
      (S : Finset V) (hS : AppbClosedSide s.graph S)
      (hn : S.Nonempty) (hc : (s.graph.atoms \ S).Nonempty) :
      NormalFineForestStep (pre++s::tail)
        (pre++ofMolecule (appbSideMolecule s.graph S hS)::
          ofMolecule (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)::tail)
  | discard (pre tail : List (State.{u,v} V)) (s : State.{u,v} V) (ht : Terminal s) :
      NormalFineForestStep (pre++s::tail) (pre++tail)

theorem NormalFineForestStep.defect_mono {F G : List (State.{u,v} V)}
    (h : NormalFineForestStep F G) : forestDefectPotential F ≤ forestDefectPotential G := by
  cases h with
  | edit pre tail h hM =>
    have hh := h.defect_mono hM
    simp only [forestDefectPotential,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega
  | split pre tail s S hS hn hc =>
    have hh := defectPotential_closed_side_add s.graph S hS
    simp only [forestDefectPotential,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    change (pre.map (fun q => defectPotential q.graph)).sum+(defectPotential s.graph+(tail.map (fun q => defectPotential q.graph)).sum) ≤
      (pre.map (fun q => defectPotential q.graph)).sum+(defectPotential (appbSideMolecule s.graph S hS)+(defectPotential (appbSideMolecule s.graph (s.graph.atoms \ S) hS.complement)+(tail.map (fun q => defectPotential q.graph)).sum))
    rw [hh]
    omega
  | discard pre tail s ht =>
    have hh := defectPotential_zero_terminal s.graph ht
    simp only [forestDefectPotential,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega

end WaveTurbulence.Mole.AppbAlgorithm
