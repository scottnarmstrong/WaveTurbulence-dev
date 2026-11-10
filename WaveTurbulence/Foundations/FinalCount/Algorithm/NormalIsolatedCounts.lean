/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeCountChange
import Mathlib.Tactic

/-! # Normal Appendix B operations do not create isolated atoms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 3D3-1N does not change the number of isolated atoms. -/
theorem d33_normal_isolated_count (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4) :
    ((appbDegreeAtoms r.post 0).card : ℤ) - (appbDegreeAtoms M 0).card = 0 := by
  have h1 : M.deg (r.vertex 1) = 3 := (r.deleted_degree 1 (by decide)).trans (by decide)
  have h2 : M.deg (r.vertex 2) = 3 := (r.deleted_degree 2 (by decide)).trans (by decide)
  have hl1 : AppbPatternKind.d33.pattern.localDegree 1 = 3 := by decide
  have hl2 : AppbPatternKind.d33.pattern.localDegree 2 = 3 := by decide
  have hl3 : AppbPatternKind.d33.pattern.localDegree 3 = 1 := by decide
  have hl4 : AppbPatternKind.d33.pattern.localDegree 4 = 1 := by decide
  have hrem : AppbPatternKind.d33.pattern.removed = {1,2} := rfl
  rw [TableDegree.post_degreeCount_difference r 0, show AppbPatternKind.d33.pattern.vertices = {1,2,3,4} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    Nat.reduceEqDiff,or_false,false_or,not_false_eq_true]
  norm_num [hrem,hl1,hl2,hl3,hl4,h1,h2,h3,h4]

end WaveTurbulence.Mole.AppbAlgorithm
