/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTwoRemovalDegrees
import Mathlib.Tactic

/-! # Degree-three effect for the common exterior neighbour in 2R-3F -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 2rprop: when both exterior bonds return to the same atom, the
source degree cap and exclusion of degree-three neighbours give Delta V3=0. -/
theorem appb_r23_common_degreeThree (M : Molecule V D)
    (r : AppbRealization M appbR23Common)
    (h4 : M.deg (r.vertex 4) ≤ 4) (hne4 : M.deg (r.vertex 4) ≠ 3) :
    ((appbDegreeAtoms r.post 3).card : ℤ)-(appbDegreeAtoms M 3).card = 0 := by
  have h1 : M.deg (r.vertex 1) = 2 := (r.deleted_degree 1 (by decide)).trans (by decide)
  have h2 : M.deg (r.vertex 2) = 2 := (r.deleted_degree 2 (by decide)).trans (by decide)
  have h3 : M.deg (r.vertex 3) = 2 := (r.deleted_degree 3 (by decide)).trans (by decide)
  have hl1 : appbR23Common.localDegree 1 = 2 := by decide
  have hl2 : appbR23Common.localDegree 2 = 2 := by decide
  have hl3 : appbR23Common.localDegree 3 = 2 := by decide
  have hl4 : appbR23Common.localDegree 4 = 2 := by decide
  have hrem : appbR23Common.removed = {1,2,3} := rfl
  have hne5 : M.deg (r.vertex 4) ≠ 5 := by omega
  rw [r.post_degreeThree_difference,show appbR23Common.vertices = {1,2,3,4} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,Finset.mem_singleton,
    Nat.reduceEqDiff,or_false,not_false_eq_true]
  norm_num [hrem,hl1,hl2,hl3,hl4,h1,h2,h3,hne4,hne5]

end WaveTurbulence.Mole
