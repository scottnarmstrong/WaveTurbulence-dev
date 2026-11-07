/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! # Distinct old-edge enumeration for two consecutive literal figures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace SequentialFigure
variable {M : Molecule V D} {P Q : AppbPattern}
    (r : AppbRealization M P) (t : AppbRealization r.post Q)

theorem old_edge_ne_retained (i : Fin P.edges.length) (x : Degen.RetainedDart M r.removedAtoms) :
    (r.edge i).val ≠ x.val := by
  intro he
  have hi := (mem_filter.mp (r.edge i).property).2
  rw [he] at hi
  rcases hi with hi | hi
  · exact x.property.1 hi
  · exact x.property.2 hi

def enumeration : Fin (P.edges.length+Q.edges.length) → D :=
  Sum.elim (fun i => (r.edge i).val) (fun i => (t.edge i).val.val) ∘ finSumFinEquiv.symm

theorem enumeration_injective : Function.Injective (enumeration r t) := by
  have hr : Function.Injective fun i => (r.edge i).val := by
    intro i j h
    exact r.edge.injective (Subtype.ext h)
  have ht : Function.Injective fun i => (t.edge i).val.val := by
    intro i j h
    apply t.edge.injective
    exact Subtype.ext (Subtype.ext h)
  exact (hr.sumElim ht (fun i j => old_edge_ne_retained r i (t.edge j).val)).comp finSumFinEquiv.symm.injective

theorem enumeration_outgoing (i : Fin (P.edges.length+Q.edges.length)) :
    M.out (enumeration r t i) = true := by
  simp only [enumeration,Function.comp_apply]
  rcases finSumFinEquiv.symm i with j | j
  · exact (mem_filter.mp (mem_filter.mp (r.edge j).property).1).2
  · exact (mem_filter.mp (mem_filter.mp (t.edge j).property).1).2

end SequentialFigure
end WaveTurbulence.Mole.AppbAlgorithm
