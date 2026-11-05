/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLBranchRealization
import Mathlib.Tactic

/-! # Parent inheritance and joint separation in pruned regions
TARGET `block_clcn`: the second CN joint is outside the first joint's
pruned descendant region, including when both joints lie in one tree.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem child_not_ancestor_self (b : GBranch G.tree) (i : Fin 3) :
    ¬ (b.child i).IsDesc b.toNode := by
  intro h
  have hl := h.2.length_le
  change (b.1.2++[i]).length ≤ b.1.2.length at hl
  simp only [List.length_append,List.length_singleton] at hl
  omega

theorem pruned_node_nonroot {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {v : GNode G.tree} (hv : InCLPrunedRegion G S a b v) (hne : v ≠ a.toNode) : v.1.2 ≠ [] := by
  intro hn
  have ha : a.1.2 = [] := List.prefix_nil.mp (hn ▸ hv.1.2)
  exact hne (Subtype.ext (Prod.ext hv.1.1.symm (hn.trans ha.symm)))

theorem pruned_parent {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {v : GNode G.tree} (hv : InCLPrunedRegion G S a b v) (hne : v ≠ a.toNode)
    (hn : v.1.2 ≠ []) :
    InCLPrunedRegion G S a b (GNode.parent v hn).toNode := by
  refine ⟨⟨hv.1.1,proper_prefix_dropLast hv.1.2 ?_⟩,?_⟩
  · intro hp
    exact hne (Subtype.ext (Prod.ext hv.1.1.symm hp.symm))
  · intro j hj i hi hd
    exact hv.2 j hj i hi ⟨hd.1,hd.2.trans (List.dropLast_prefix _)⟩

/-- A selected joint whose parent is outside cannot lie in the other
joint's once-pruned subtree. This is the CN separation alternative. -/
theorem cn_joint_separation {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hb : ¬ InternalParent G S b)
    (hd : a.toNode.IsDesc b.toNode) :
    ∃ i : Fin 3, i.succ ∉ internalPositions G S a ∧ (a.child i).IsDesc b.toNode := by
  classical
  by_contra hn
  have hcut : ∀ i : Fin 3, i.succ ∉ internalPositions G S a → ¬ (a.child i).IsDesc b.toNode := by
    intro i hi hiDesc
    exact hn ⟨i,hi,hiDesc⟩
  have hr : InCLPrunedRegion G S a b b.toNode := by
    refine ⟨hd,?_⟩
    intro j hj i hi
    simp only [mem_insert,mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact hcut i hi
    · exact child_not_ancestor_self G _ i
  have hne : b.toNode ≠ a.toNode := fun he => hB.2.2.2.1 (branch_toNode_injective he).symm
  have hn := pruned_node_nonroot G hr hne
  have hp := pruned_parent G hr hne hn
  exact hb ⟨hn,joint_pruned_branch_mem G hB _ hp⟩

end WaveTurbulence.Mole
