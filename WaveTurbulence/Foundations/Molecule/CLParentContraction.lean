/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SpliceInsideNodes
import Mathlib.Tactic

/-! # Parent endpoints commute with CL atom contraction
TARGET `block_clcn` (2). Inside a boundary subtree, parent addresses
transport unchanged; at its root, the old joint becomes the new crown.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} (G : Garden w)

theorem parent_child_branch_eq (c : GBranch G.tree) (i : Fin 3)
    (hn : (c.child i).1.2 ≠ []) : GNode.parent (c.child i) hn = c := by
  apply Subtype.ext
  exact Prod.ext rfl (by
    change (c.1.2++[i]).dropLast = c.1.2
    rw [List.dropLast_append_cons,List.dropLast_singleton,List.append_nil])

theorem parent_outside_of_node_outside {a : GBranch G.tree} (n : GNode G.tree)
    (hn : n.1.2 ≠ []) (hout : ¬ a.toNode.IsDesc n) :
    ¬ a.toNode.IsDesc (GNode.parent n hn).toNode := by
  intro hd
  exact hout ⟨hd.1,hd.2.trans (List.dropLast_prefix _)⟩

theorem branch_not_ancestor_parent (a : GBranch G.tree) (hn : a.1.2 ≠ []) :
    ¬ a.toNode.IsDesc (GNode.parent a.toNode hn).toNode := by
  intro hd
  have hl := hd.2.length_le
  change a.1.2.length ≤ a.1.2.dropLast.length at hl
  rw [List.length_dropLast] at hl
  have hp := List.length_pos_of_ne_nil hn
  omega

variable {G} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

theorem clSpliceBoundary_parent_mem (i : Fin 3)
    (hn : ((clSpliceBoundary hB hCL D).node i).1.2 ≠ []) :
    GNode.parent ((clSpliceBoundary hB hCL D).node i) hn ∈ S := by
  have hbase : ∀ j : Fin 3, ∀ hn : (clBaseBoundary a b D.excluded D.kept j).1.2 ≠ [],
      GNode.parent (clBaseBoundary a b D.excluded D.kept j) hn ∈ S := by
    intro j hn
    fin_cases j
    · exact (parent_child_branch_eq G a D.excluded hn).symm ▸ hB.2.1
    · exact (parent_child_branch_eq G b 1 hn).symm ▸ hB.2.2.1
    · exact (parent_child_branch_eq G b (otherOuterChild D.kept) hn).symm ▸ hB.2.2.1
  exact hbase (clBoundarySelector D.excluded (clSameSign a b) i) hn

theorem cl_parent_contract_outside (nOld : GNode G.tree)
    (nNew : GNode (clSplicedGardenOfSlots hB hCL D).tree)
    (he : nNew.1 = nOld.1) (ho : nOld.1.2 ≠ []) (hn : nNew.1.2 ≠ [])
    (hout : ¬ a.toNode.IsDesc (GNode.parent nOld ho).toNode) :
    contractVertex S (GNode.parent nOld ho) =
      clSplicedBranchEquiv hB hCL D (GNode.parent nNew hn) := by
  let p := GNode.parent nOld ho
  let piece : SpliceBranchPiece (clSpliceBoundary hB hCL D) := .inl ⟨p,hout⟩
  have hp : p ∉ S := (clSpliceRetainedBranch_iff hB hCL D p).mp (Or.inl hout)
  have heparent : GNode.parent nNew hn = spliceBranchPieceNew (clSpliceBoundary hB hCL D) piece := by
    apply Subtype.ext
    change (nNew.1.1,nNew.1.2.dropLast) = (nOld.1.1,nOld.1.2.dropLast)
    exact congrArg (fun p : Fin w × Path => (p.1,p.2.dropLast)) he
  rw [heparent,clSplicedBranchEquiv_piece]
  exact dite_eq_right hp

theorem cl_parent_contract_inside (i : Fin 3) (q : Path)
    (hq : q ∈ (spliceNodeSubtree G ((clSpliceBoundary hB hCL D).node i)).nodes)
    (ho : (spliceOldInsideNode (clSpliceBoundary hB hCL D) i q hq).1.2 ≠ [])
    (hn : (spliceNewInsideNode (clSpliceBoundary hB hCL D) i q hq).1.2 ≠ []) :
    contractVertex S (GNode.parent (spliceOldInsideNode (clSpliceBoundary hB hCL D) i q hq) ho) =
      clSplicedBranchEquiv hB hCL D
        (GNode.parent (spliceNewInsideNode (clSpliceBoundary hB hCL D) i q hq) hn) := by
  let f : GBranch (spliceForest G a (clSpliceBoundary hB hCL D).node) → ContractVertex S :=
    clSplicedBranchEquiv hB hCL D
  by_cases hqne : q = []
  · subst q
    have heNew := parent_spliceNewInside_nil (clSpliceBoundary hB hCL D) i hq hn
    have hnew : f (GNode.parent (spliceNewInsideNode (clSpliceBoundary hB hCL D) i [] hq) hn) = none :=
      (congrArg f heNew).trans (clSplicedBranchEquiv_crown hB hCL D)
    have he : GNode.parent (spliceOldInsideNode (clSpliceBoundary hB hCL D) i [] hq) ho =
        GNode.parent ((clSpliceBoundary hB hCL D).node i) (clSpliceBoundary_nonroot hB hCL D i) := by
      apply Subtype.ext
      exact Prod.ext rfl (by simp only [spliceOldInsideNode,GNode.parent,List.append_nil])
    have hold : contractVertex S (GNode.parent (spliceOldInsideNode (clSpliceBoundary hB hCL D) i [] hq) ho) = none :=
      (contractVertex_eq_none S _).mpr (he.symm ▸ clSpliceBoundary_parent_mem hB hCL D i _)
    exact hold.trans hnew.symm
  · let p : SpliceBranchPiece (clSpliceBoundary hB hCL D) :=
      .inr ⟨i,⟨q.dropLast,TTree.dropLast_mem_branching hq hqne⟩⟩
    have heOld := parent_spliceOldInside_nonempty (clSpliceBoundary hB hCL D) i q hq hqne ho
    have heNew := parent_spliceNewInside_nonempty (clSpliceBoundary hB hCL D) i q hq hqne hn
    have hp := (clSpliceRetainedBranch_iff hB hCL D _).mp
      (spliceBranchPieceOld_retained (clSpliceBoundary hB hCL D) p)
    calc
      _ = contractVertex S (spliceBranchPieceOld (clSpliceBoundary hB hCL D) p) :=
        congrArg (contractVertex S) heOld
      _ = some ⟨spliceBranchPieceOld (clSpliceBoundary hB hCL D) p,hp⟩ := dite_eq_right hp
      _ = f (spliceBranchPieceNew (clSpliceBoundary hB hCL D) p) :=
        (clSplicedBranchEquiv_piece hB hCL D p).symm
      _ = _ := congrArg f heNew.symm

end WaveTurbulence.Mole
