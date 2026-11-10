/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockTypes
import Mathlib.Tactic

/-! # The excluded and retained child indices at CL/CN joints
TARGET `block_clcn` (CL)(i), (CN)(i): every single excluded child and
the single retained child have the same sign as their branching parent.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem no_parent_joint_excluded_child {S : Finset (GBranch G.tree)} {v : GBranch G.tree}
    (hv : v ∈ S) (ho : G.molecule.outIn S v = 1) (hi : G.molecule.inIn S v = 1)
    (hn : ¬ InternalParent G S v) :
    ∃ k : Fin 3, k ≠ 1 ∧ ∀ i : Fin 3,
      i.succ ∈ internalPositions G S v ↔ i ≠ k := by
  rcases joint_no_parent_slots G hv ho hi hn with h | h
  · refine ⟨2,by decide,?_⟩
    rw [h]
    decide
  · refine ⟨0,by decide,?_⟩
    rw [h]
    decide

theorem with_parent_joint_retained_child {S : Finset (GBranch G.tree)} {v : GBranch G.tree}
    (hv : v ∈ S) (ho : G.molecule.outIn S v = 1) (hi : G.molecule.inIn S v = 1)
    (hn : InternalParent G S v) :
    ∃ k : Fin 3, k ≠ 1 ∧ ∀ i : Fin 3,
      i.succ ∈ internalPositions G S v ↔ i = k := by
  rcases joint_with_parent_slots G hv ho hi hn with h | h
  · refine ⟨0,by decide,?_⟩
    rw [h]
    decide
  · refine ⟨2,by decide,?_⟩
    rw [h]
    decide

theorem outer_child_sign (v : GBranch G.tree) (i : Fin 3) (hi : i ≠ 1) :
    G.sign (v.child i) = G.sign v.toNode := by
  fin_cases i
  · simp [Garden.sign,nodeSign,TTree.pathSign,GBranch.child,List.count_append,GBranch.toNode]
  · exact (hi rfl).elim
  · simp [Garden.sign,nodeSign,TTree.pathSign,GBranch.child,List.count_append,GBranch.toNode]

end WaveTurbulence.Mole
