/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionForest

/-! # Exact leaf, branch and lone-subtree equations of reconstruction -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.inflateNode_leaf {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (ℓ : GLeaf S.tree) : D.inflateNode hS ℓ.toNode = D.leafTree hS ℓ := by
  rw [ReconstructionData.inflateNode]
  split
  next ha =>
    congr 1
  next l m r ha =>
    have hl := nodeSubtree_leaf S.tree ℓ
    rw [hl] at ha
    cases ha

theorem ReconstructionData.inflateNode_branch {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) :
    D.inflateNode hS b.toNode = (D.tree b).plug (nodeSign S.sig b.1)
      (node3 (fun i => D.inflateNode hS (b.child i))) := by
  rw [ReconstructionData.inflateNode]
  split
  next ha =>
    have hb : [] ∈ (Comb.nodeSubtree b.toNode).branching :=
      (Comb.subtree_branching_iff (Comb.nodeSubtree_spec b.toNode) []).mpr (by rw [List.append_nil]; exact b.2)
    rw [ha] at hb
    exact (Finset.notMem_empty _ hb).elim
  next l m r ha =>
    have hb : branchOfSubtree b.toNode l m r ha = b := Subtype.ext rfl
    simp only [hb]
    rfl

/-- The original branching node lies exactly at the regular replacement's lone path. -/
theorem ReconstructionData.inflateNode_subtree_lone {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) :
    Comb.subtree (D.inflateNode hS b.toNode) (D.tree b).lonePath =
      some (node3 (fun i => D.inflateNode hS (b.child i))) := by
  rw [D.inflateNode_branch hS b]
  exact plug_subtree_lonePath _ _ _

/-- Every actual original child begins just below that lone path, in its original ordered slot. -/
theorem ReconstructionData.inflateNode_subtree_child {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) (i : Fin 3) :
    Comb.subtree (D.inflateNode hS b.toNode) ((D.tree b).lonePath ++ [i]) =
      some (D.inflateNode hS (b.child i)) := by
  rw [Comb.subtree_append,D.inflateNode_subtree_lone hS b]
  fin_cases i <;> simp [node3,Comb.subtree]

end WaveTurbulence.Reg.Skeleton
