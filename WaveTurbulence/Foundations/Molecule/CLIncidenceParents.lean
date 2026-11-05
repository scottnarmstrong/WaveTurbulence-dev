/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLParentContraction
public import WaveTurbulence.Foundations.Molecule.CLLeafNames
import Mathlib.Tactic

/-! # Actual PC and LP parent endpoints under the constructed splice -/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

theorem parent_congr_of_node_eq {n m : GNode tree} (he : n = m)
    (hn : n.1.2 ≠ []) (hm : m.1.2 ≠ []) : GNode.parent n hn = GNode.parent m hm := by
  cases he
  rfl

variable {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

theorem cl_branch_piece_parent_contract (p : SpliceBranchPiece (clSpliceBoundary hB hCL D))
    (ho : (spliceBranchPieceOld (clSpliceBoundary hB hCL D) p).1.2 ≠ [])
    (hn : (spliceBranchPieceNew (clSpliceBoundary hB hCL D) p).1.2 ≠ []) :
    contractVertex S (GNode.parent (spliceBranchPieceOld (clSpliceBoundary hB hCL D) p).toNode ho) =
      clSplicedBranchEquiv hB hCL D
        (GNode.parent (spliceBranchPieceNew (clSpliceBoundary hB hCL D) p).toNode hn) := by
  cases p with
  | inl c =>
    exact cl_parent_contract_outside hB hCL D c.1.toNode _ rfl ho hn
      (parent_outside_of_node_outside G c.1.toNode ho c.2)
  | inr p =>
    exact cl_parent_contract_inside hB hCL D p.1 p.2.1
      (TTree.branching_subset_nodes _ p.2.2) ho hn

theorem cl_leaf_piece_parent_contract (p : SpliceLeafPiece (clSpliceBoundary hB hCL D))
    (ho : (splicePieceOld (clSpliceBoundary hB hCL D) p).1.2 ≠ [])
    (hn : (splicePieceNew (clSpliceBoundary hB hCL D) p).1.2 ≠ []) :
    contractVertex S (GNode.parent (splicePieceOld (clSpliceBoundary hB hCL D) p).toNode ho) =
      clSplicedBranchEquiv hB hCL D
        (GNode.parent (splicePieceNew (clSpliceBoundary hB hCL D) p).toNode hn) := by
  cases p with
  | inl l =>
    exact cl_parent_contract_outside hB hCL D l.1.toNode _ rfl ho hn
      (parent_outside_of_node_outside G l.1.toNode ho l.2)
  | inr p =>
    exact cl_parent_contract_inside hB hCL D p.1 p.2.1
      (TTree.leaves_subset_nodes _ p.2.2) ho hn

theorem cl_branch_name_parent_contract (c : GBranch (clSplicedGardenOfSlots hB hCL D).tree)
    (hn : c.1.2 ≠ []) (ho : (clSplicedBranchNameEquiv hB hCL D c).1.1.2 ≠ []) :
    contractVertex S (GNode.parent (clSplicedBranchNameEquiv hB hCL D c).1.toNode ho) =
      clSplicedBranchEquiv hB hCL D (GNode.parent c.toNode hn) := by
  classical
  by_cases hc : c = spliceCrownBranch (clSpliceBoundary hB hCL D)
  · subst c
    have he := clSplicedBranchName_crown hB hCL D
    have hao : a.1.2 ≠ [] := fun h => ho ((congrArg (fun c : GBranch G.tree => c.1.2) he).trans h)
    have hp := parent_congr_of_node_eq (congrArg GBranch.toNode he) ho hao
    exact (congrArg (contractVertex S) hp).trans
      (cl_parent_contract_outside hB hCL D a.toNode _ rfl hao hn (branch_not_ancestor_parent G a hao))
  · obtain ⟨p,rfl⟩ := spliceBranchPieceNew_surjective_except_crown (clSpliceBoundary hB hCL D) c hc
    have he := clSplicedBranchName_piece hB hCL D p
    have hop : (spliceBranchPieceOld (clSpliceBoundary hB hCL D) p).1.2 ≠ [] :=
      fun h => ho ((congrArg (fun c : GBranch G.tree => c.1.2) he).trans h)
    have hp := parent_congr_of_node_eq (congrArg GBranch.toNode he) ho hop
    exact (congrArg (contractVertex S) hp).trans (cl_branch_piece_parent_contract hB hCL D p hop hn)

theorem cl_leaf_name_parent_contract (l : GLeaf (clSplicedGardenOfSlots hB hCL D).tree)
    (hn : l.1.2 ≠ []) (ho : (clSplicedLeafNameEquiv hB hCL D l).1.1.2 ≠ []) :
    contractVertex S (GNode.parent (clSplicedLeafNameEquiv hB hCL D l).1.toNode ho) =
      clSplicedBranchEquiv hB hCL D (GNode.parent l.toNode hn) := by
  obtain ⟨p,rfl⟩ := splicePieceNew_surjective (clSpliceBoundary hB hCL D) l
  have he := spliceLeafEquiv_piece (clSpliceBoundary hB hCL D) p
  have hop : (splicePieceOld (clSpliceBoundary hB hCL D) p).1.2 ≠ [] :=
    fun h => ho ((congrArg (fun l : GLeaf G.tree => l.1.2) he).trans h)
  have hp := parent_congr_of_node_eq (congrArg GLeaf.toNode he) ho hop
  exact (congrArg (contractVertex S) hp).trans (cl_leaf_piece_parent_contract hB hCL D p hop hn)

end WaveTurbulence.Mole
