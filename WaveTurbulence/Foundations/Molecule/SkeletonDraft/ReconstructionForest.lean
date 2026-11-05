/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionData
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceMiniShapes

/-! # Literal ordered forest obtained from regular replacement codes -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- A source node with leaf subtree is an actual source leaf. -/
def leafOfSubtree {w : ℕ} {S : Garden w} (a : GNode S.tree)
    (ha : Comb.nodeSubtree a = .leaf) : GLeaf S.tree :=
  ⟨a.1,by
    have hl := (Comb.subtree_leaves_iff (Comb.nodeSubtree_spec a) []).mp
      (by rw [ha]; exact Finset.mem_singleton_self _)
    simpa only [List.append_nil] using hl⟩

/-- A source node with a branching subtree is an actual source branch. -/
def branchOfSubtree {w : ℕ} {S : Garden w} (a : GNode S.tree) (l m r : TTree)
    (ha : Comb.nodeSubtree a = .node l m r) : GBranch S.tree :=
  ⟨a.1,by
    have hb := (Comb.subtree_branching_iff (Comb.nodeSubtree_spec a) []).mp
      (by rw [ha]; simp [TTree.branching])
    simpa only [List.append_nil] using hb⟩

theorem nodeSubtree_child_order_lt {w : ℕ} (tree : Fin w → TTree) (b : GBranch tree) (i : Fin 3) :
    (Comb.nodeSubtree (b.child i)).order < (Comb.nodeSubtree b.toNode).order := by
  rw [nodeSubtree_branch tree b]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp only [node3,TTree.order] <;> omega

/-- Inflate every actual branch above its original ordered children and every leaf by its
shared regular-couple sign side. The recursion is on the original source subtree order. -/
noncomputable def ReconstructionData.inflateNode {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (a : GNode S.tree) : TTree :=
  match ha : Comb.nodeSubtree a with
  | .leaf => D.leafTree hS (leafOfSubtree a ha)
  | .node l m r =>
    let b := branchOfSubtree a l m r ha
    (D.tree b).plug (nodeSign S.sig a.1) (node3 (fun i => D.inflateNode hS (b.child i)))
termination_by (Comb.nodeSubtree a).order
decreasing_by exact nodeSubtree_child_order_lt S.tree _ _

/-- The fully decoded ordered forest; original roots and root signature are retained. -/
noncomputable def ReconstructionData.forest {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : Fin w → TTree := fun j => D.inflateNode hS (GNode.root S.tree j)

/-- Literal raw reconstruction, with canonical finite internal matching from all replacements. -/
noncomputable def ReconstructionData.raw {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : Raw w := ⟨S.sig,D.forest hS,D.attachmentPairs hS⟩

/-- An ordinary actual target garden with exactly the decoded forest and complete oriented matching. -/
def ReconstructionData.Decodes {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (G : Garden w) : Prop := G.IsPlain ∧ D.raw hS = rawOfGarden G

end WaveTurbulence.Reg.Skeleton
