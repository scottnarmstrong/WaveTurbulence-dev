/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ParentRegions
import Mathlib.Tactic

/-! # Intrinsic parent-flow types and their exact joint slots

DH23 Proposition 4.12: CL has one parent incidence inside, CN has none.
The geometric realization equivalence is a separate proof obligation.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- Oriented CL parent pattern, with upper joint `a` and lower joint `b`. -/
@[expose] def CLParentPattern (S : Finset (GBranch G.tree)) (a b : GBranch G.tree) : Prop :=
  ¬ InternalParent G S a ∧ InternalParent G S b

/-- CN parent pattern; both joint parents lie outside the block. -/
@[expose] def CNParentPattern (S : Finset (GBranch G.tree)) (a b : GBranch G.tree) : Prop :=
  ¬ InternalParent G S a ∧ ¬ InternalParent G S b

theorem block_parent_patterns {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) :
    CLParentPattern G S a b ∨ CLParentPattern G S b a ∨ CNParentPattern G S a b := by
  have hd := block_parent_dichotomy G hB
  unfold CLParentPattern CNParentPattern
  tauto

theorem joint_no_parent_slots {S : Finset (GBranch G.tree)} {v : GBranch G.tree}
    (hv : v ∈ S) (ho : G.molecule.outIn S v = 1) (hi : G.molecule.inIn S v = 1)
    (hn : ¬ InternalParent G S v) :
    internalPositions G S v = {1,2} ∨ internalPositions G S v = {2,3} := by
  have hz : 0 ∉ internalPositions G S v := fun h => hn ((zero_mem_internalPositions G hv).mp h)
  rcases joint_positions_shape G ho hi with h | h | h | h
  · rw [h] at hz
    exact (hz (by simp)).elim
  · rw [h] at hz
    exact (hz (by simp)).elim
  · exact Or.inl h
  · exact Or.inr h

theorem joint_with_parent_slots {S : Finset (GBranch G.tree)} {v : GBranch G.tree}
    (hv : v ∈ S) (ho : G.molecule.outIn S v = 1) (hi : G.molecule.inIn S v = 1)
    (hn : InternalParent G S v) :
    internalPositions G S v = {0,1} ∨ internalPositions G S v = {0,3} := by
  have hz := (zero_mem_internalPositions G hv).mpr hn
  rcases joint_positions_shape G ho hi with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rw [h] at hz
    norm_num at hz
  · rw [h] at hz
    norm_num at hz

/-- The lower CL joint is a strict actual descendant of the upper joint. -/
theorem cl_parent_strict_descendant {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) :
    a.toNode.IsDesc b.toNode ∧ a.1.2.length < b.1.2.length := by
  refine ⟨block_one_root_descendants G hB hCL.1 hCL.2 hB.2.2.1,?_⟩
  have hswap : G.molecule.IsBlock S b a := block_swap_joints G.molecule hB
  exact internal_parent_joint_length G hswap hCL.2

end WaveTurbulence.Mole
