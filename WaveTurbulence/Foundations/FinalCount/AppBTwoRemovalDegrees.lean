/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDegreeThree
import Mathlib.Tactic

/-! # DH23 2rprop: exact degree-three changes of fine operations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 2rprop, r21 incidence pattern: exact V3 effect. -/
theorem appb_r21_degreeThree (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r21.pattern)
    (h2 : M.deg (r.vertex 2) = 4)
    : ((appbDegreeAtoms r.post 3).card : ℤ) - (appbDegreeAtoms M 3).card = 0 := by
  have h1 : M.deg (r.vertex 1) = 2 := (r.deleted_degree 1 (by decide)).trans (by decide)
  have hl1 : AppbPatternKind.r21.pattern.localDegree 1 = 2 := by decide
  have hl2 : AppbPatternKind.r21.pattern.localDegree 2 = 2 := by decide
  have hrem : AppbPatternKind.r21.pattern.removed = {1} := rfl
  rw [r.post_degreeThree_difference, show AppbPatternKind.r21.pattern.vertices = {1,2} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    Nat.reduceEqDiff,or_false,not_false_eq_true]
  norm_num [hrem,hl1,hl2,h1,h2]

/-- DH23 2rprop, r24 incidence pattern: exact V3 effect. -/
theorem appb_r24_degreeThree (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r24.pattern)
    : ((appbDegreeAtoms r.post 3).card : ℤ) - (appbDegreeAtoms M 3).card = 0 := by
  have h1 : M.deg (r.vertex 1) = 2 := (r.deleted_degree 1 (by decide)).trans (by decide)
  have h2 : M.deg (r.vertex 2) = 2 := (r.deleted_degree 2 (by decide)).trans (by decide)
  have hl1 : AppbPatternKind.r24.pattern.localDegree 1 = 2 := by decide
  have hl2 : AppbPatternKind.r24.pattern.localDegree 2 = 2 := by decide
  have hrem : AppbPatternKind.r24.pattern.removed = {1,2} := rfl
  rw [r.post_degreeThree_difference, show AppbPatternKind.r24.pattern.vertices = {1,2} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    Nat.reduceEqDiff,or_false,not_false_eq_true]
  norm_num [hrem,hl1,hl2,h1,h2]

/-- DH23 2rprop, r23triangle incidence pattern: exact V3 effect. -/
theorem appb_r23triangle_degreeThree (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r23triangle.pattern)
    : ((appbDegreeAtoms r.post 3).card : ℤ) - (appbDegreeAtoms M 3).card = 0 := by
  have h1 : M.deg (r.vertex 1) = 2 := (r.deleted_degree 1 (by decide)).trans (by decide)
  have h2 : M.deg (r.vertex 2) = 2 := (r.deleted_degree 2 (by decide)).trans (by decide)
  have h3 : M.deg (r.vertex 3) = 2 := (r.deleted_degree 3 (by decide)).trans (by decide)
  have hl1 : AppbPatternKind.r23triangle.pattern.localDegree 1 = 2 := by decide
  have hl2 : AppbPatternKind.r23triangle.pattern.localDegree 2 = 2 := by decide
  have hl3 : AppbPatternKind.r23triangle.pattern.localDegree 3 = 2 := by decide
  have hrem : AppbPatternKind.r23triangle.pattern.removed = {1,2,3} := rfl
  rw [r.post_degreeThree_difference, show AppbPatternKind.r23triangle.pattern.vertices = {1,2,3} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    Nat.reduceEqDiff,or_false,not_false_eq_true]
  norm_num [hrem,hl1,hl2,hl3,h1,h2,h3]

/-- DH23 2rprop, r22 incidence pattern: exact V3 effect. -/
theorem appb_r22_degreeThree (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r22.pattern)
    (h2 : M.deg (r.vertex 2) = 4) (h3 : M.deg (r.vertex 3) = 2 ∨ M.deg (r.vertex 3) = 4)
    : ((appbDegreeAtoms r.post 3).card : ℤ) - (appbDegreeAtoms M 3).card = (if M.deg (r.vertex 3) = 4 then 2 else 1) := by
  have h1 : M.deg (r.vertex 1) = 2 := (r.deleted_degree 1 (by decide)).trans (by decide)
  have hl1 : AppbPatternKind.r22.pattern.localDegree 1 = 2 := by decide
  have hl2 : AppbPatternKind.r22.pattern.localDegree 2 = 1 := by decide
  have hl3 : AppbPatternKind.r22.pattern.localDegree 3 = 1 := by decide
  have hrem : AppbPatternKind.r22.pattern.removed = {1} := rfl
  rw [r.post_degreeThree_difference, show AppbPatternKind.r22.pattern.vertices = {1,2,3} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    Nat.reduceEqDiff,or_false,not_false_eq_true]
  rcases h3 with h3 | h3
  <;> norm_num [hrem,hl1,hl2,hl3,h1,h2,h3]

/-- DH23 2rprop, r23 incidence pattern: exact V3 effect. -/
theorem appb_r23_degreeThree (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r23.pattern)
    (h4 : M.deg (r.vertex 4) ≠ 3) (h5 : M.deg (r.vertex 5) ≠ 3)
    : ((appbDegreeAtoms r.post 3).card : ℤ) - (appbDegreeAtoms M 3).card = (if M.deg (r.vertex 4) = 4 then 1 else 0) + (if M.deg (r.vertex 5) = 4 then 1 else 0) := by
  have h1 : M.deg (r.vertex 1) = 2 := (r.deleted_degree 1 (by decide)).trans (by decide)
  have h2 : M.deg (r.vertex 2) = 2 := (r.deleted_degree 2 (by decide)).trans (by decide)
  have h3 : M.deg (r.vertex 3) = 2 := (r.deleted_degree 3 (by decide)).trans (by decide)
  have hl1 : AppbPatternKind.r23.pattern.localDegree 1 = 2 := by decide
  have hl2 : AppbPatternKind.r23.pattern.localDegree 2 = 2 := by decide
  have hl3 : AppbPatternKind.r23.pattern.localDegree 3 = 2 := by decide
  have hl4 : AppbPatternKind.r23.pattern.localDegree 4 = 1 := by decide
  have hl5 : AppbPatternKind.r23.pattern.localDegree 5 = 1 := by decide
  have hrem : AppbPatternKind.r23.pattern.removed = {1,2,3} := rfl
  rw [r.post_degreeThree_difference, show AppbPatternKind.r23.pattern.vertices = {1,2,3,4,5} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    Nat.reduceEqDiff,or_false,not_false_eq_true]
  norm_num [hrem,hl1,hl2,hl3,hl4,hl5,h1,h2,h3,h4,h5]

end WaveTurbulence.Mole
