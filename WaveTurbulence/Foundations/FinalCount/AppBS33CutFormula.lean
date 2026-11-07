/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalCuts
import Mathlib.Tactic

/-! # The five literal crossing tests for the distinct-neighbor single pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_s33_cut_formula {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (S : Finset V) :
    r.cutCount S =
      (if (r.vertex 1 ∈ S ∧ r.vertex 2 ∉ S) ∨ (r.vertex 1 ∉ S ∧ r.vertex 2 ∈ S) then 1 else 0)+
      (if (r.vertex 1 ∈ S ∧ r.vertex 3 ∉ S) ∨ (r.vertex 1 ∉ S ∧ r.vertex 3 ∈ S) then 1 else 0)+
      (if (r.vertex 1 ∈ S ∧ r.vertex 4 ∉ S) ∨ (r.vertex 1 ∉ S ∧ r.vertex 4 ∈ S) then 1 else 0)+
      (if (r.vertex 2 ∈ S ∧ r.vertex 5 ∉ S) ∨ (r.vertex 2 ∉ S ∧ r.vertex 5 ∈ S) then 1 else 0)+
      (if (r.vertex 2 ∈ S ∧ r.vertex 6 ∉ S) ∨ (r.vertex 2 ∉ S ∧ r.vertex 6 ∈ S) then 1 else 0) := by
  classical
  change (∑ i : Fin 5,if
    (r.vertex ([(1,2),(1,3),(1,4),(2,5),(2,6)][i].1) ∈ S ∧
      r.vertex ([(1,2),(1,3),(1,4),(2,5),(2,6)][i].2) ∉ S) ∨
    (r.vertex ([(1,2),(1,3),(1,4),(2,5),(2,6)][i].1) ∉ S ∧
      r.vertex ([(1,2),(1,3),(1,4),(2,5),(2,6)][i].2) ∈ S) then 1 else 0) = _
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  dsimp
  omega

end WaveTurbulence.Mole
