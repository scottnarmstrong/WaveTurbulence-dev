/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDegreeThree
import Mathlib.Tactic

/-! # The exact V3 effects of the normal Appendix B operations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 3s3prop: four degree-four boundary atoms become degree three,
while the two deleted degree-three atoms disappear. -/
theorem appb_s33_normal_degreeThree (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4)
    (h5 : M.deg (r.vertex 5) = 4) (h6 : M.deg (r.vertex 6) = 4) :
    ((appbDegreeAtoms r.post 3).card : ℤ) - (appbDegreeAtoms M 3).card = 2 := by
  have h1 : M.deg (r.vertex 1) = 3 := (r.deleted_degree 1 (by decide)).trans (by decide)
  have h2 : M.deg (r.vertex 2) = 3 := (r.deleted_degree 2 (by decide)).trans (by decide)
  have hl1 : AppbPatternKind.s33.pattern.localDegree 1 = 3 := by decide
  have hl2 : AppbPatternKind.s33.pattern.localDegree 2 = 3 := by decide
  have hl3 : AppbPatternKind.s33.pattern.localDegree 3 = 1 := by decide
  have hl4 : AppbPatternKind.s33.pattern.localDegree 4 = 1 := by decide
  have hl5 : AppbPatternKind.s33.pattern.localDegree 5 = 1 := by decide
  have hl6 : AppbPatternKind.s33.pattern.localDegree 6 = 1 := by decide
  have hrem : AppbPatternKind.s33.pattern.removed = {1,2} := rfl
  rw [r.post_degreeThree_difference, show AppbPatternKind.s33.pattern.vertices = {1,2,3,4,5,6} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    Nat.reduceEqDiff,or_false,false_or,not_false_eq_true]
  norm_num [hrem,hl1,hl2,hl3,hl4,hl5,hl6,h1,h2,h3,h4,h5,h6]

/-- DH23 3d3prop: deleting the degree-three double pair replaces it by two
new degree-three boundary atoms, so the V3 change is zero. -/
theorem appb_d33_normal_degreeThree (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4) :
    ((appbDegreeAtoms r.post 3).card : ℤ) - (appbDegreeAtoms M 3).card = 0 := by
  have h1 : M.deg (r.vertex 1) = 3 := (r.deleted_degree 1 (by decide)).trans (by decide)
  have h2 : M.deg (r.vertex 2) = 3 := (r.deleted_degree 2 (by decide)).trans (by decide)
  have hl1 : AppbPatternKind.d33.pattern.localDegree 1 = 3 := by decide
  have hl2 : AppbPatternKind.d33.pattern.localDegree 2 = 3 := by decide
  have hl3 : AppbPatternKind.d33.pattern.localDegree 3 = 1 := by decide
  have hl4 : AppbPatternKind.d33.pattern.localDegree 4 = 1 := by decide
  have hrem : AppbPatternKind.d33.pattern.removed = {1,2} := rfl
  rw [r.post_degreeThree_difference, show AppbPatternKind.d33.pattern.vertices = {1,2,3,4} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    Nat.reduceEqDiff,or_false,false_or,not_false_eq_true]
  norm_num [hrem,hl1,hl2,hl3,hl4,h1,h2,h3,h4]

/-- DH23 3rprop: three degree-four neighbours become degree three and the
single degree-three atom disappears. -/
theorem appb_r3_normal_degreeThree (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (h2 : M.deg (r.vertex 2) = 4) (h3 : M.deg (r.vertex 3) = 4)
    (h4 : M.deg (r.vertex 4) = 4) :
    ((appbDegreeAtoms r.post 3).card : ℤ) - (appbDegreeAtoms M 3).card = 2 := by
  have h1 : M.deg (r.vertex 1) = 3 := (r.deleted_degree 1 (by decide)).trans (by decide)
  have hl1 : AppbPatternKind.r3.pattern.localDegree 1 = 3 := by decide
  have hl2 : AppbPatternKind.r3.pattern.localDegree 2 = 1 := by decide
  have hl3 : AppbPatternKind.r3.pattern.localDegree 3 = 1 := by decide
  have hl4 : AppbPatternKind.r3.pattern.localDegree 4 = 1 := by decide
  have hrem : AppbPatternKind.r3.pattern.removed = {1} := rfl
  rw [r.post_degreeThree_difference, show AppbPatternKind.r3.pattern.vertices = {1,2,3,4} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    Nat.reduceEqDiff,or_false,false_or,not_false_eq_true]
  norm_num [hrem,hl1,hl2,hl3,hl4,h1,h2,h3,h4]

end WaveTurbulence.Mole
