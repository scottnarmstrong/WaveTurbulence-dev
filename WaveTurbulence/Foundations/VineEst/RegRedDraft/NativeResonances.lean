/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeSigns
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CollapsedDecorations

/-! # Exact resonance transport on core branches and actual regular replacements -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem subforest_omega {w v d : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired E.leafSet) (k : GNode G.tree → Mom d) (b : GBranch E.shape) :
    omegaNode G k (subforestBranchEmbedding E b) =
      omegaNode (E.inducedGarden hc) (fun a => k (E.nodeEmbedding a)) b := by
  change resFactor (k ((subforestBranchEmbedding E b).child 0))
    (k ((subforestBranchEmbedding E b).child 1)) (k ((subforestBranchEmbedding E b).child 2))
    (k (subforestBranchEmbedding E b).toNode) =
      resFactor (k (E.nodeEmbedding (b.child 0))) (k (E.nodeEmbedding (b.child 1)))
        (k (E.nodeEmbedding (b.child 2))) (k (E.nodeEmbedding b.toNode))
  rw [subforest_node_child,subforest_node_child,subforest_node_child,subforest_branch_node]

theorem chain_omega {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (k : GNode (D.forest hS) → Mom d) (b : GBranch S.tree)
    (q : GBranch (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) :
    omegaNode (D.garden hS) k (chainContextBranch D hS b ⟨q.1.2,q.2⟩) =
      omegaNode (decodedTree (D.tree b) (nodeSign S.sig b.1))
        (fun a => k (chainContextNode D hS b a)) q := by
  change resFactor (k ((chainContextBranch D hS b ⟨q.1.2,q.2⟩).child 0))
    (k ((chainContextBranch D hS b ⟨q.1.2,q.2⟩).child 1))
    (k ((chainContextBranch D hS b ⟨q.1.2,q.2⟩).child 2))
    (k (chainContextNode D hS b q.toNode)) =
      resFactor (k (chainContextNode D hS b (q.child 0)))
        (k (chainContextNode D hS b (q.child 1))) (k (chainContextNode D hS b (q.child 2)))
        (k (chainContextNode D hS b q.toNode))
  congr 1
  · exact (congrArg k (chainContextNode_child D hS b q 0)).symm
  · exact (congrArg k (chainContextNode_child D hS b q 1)).symm
  · exact (congrArg k (chainContextNode_child D hS b q 2)).symm

/-- Conservation in the actual regular context makes the surviving core
resonance precisely the original skeleton resonance. -/
theorem core_omega {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (k : GNode (D.forest hS) → Mom d)
    (hk : IsDecoration (D.garden hS) k) (b : GBranch S.tree) :
    omegaNode (D.garden hS) k (D.coreBranch hS b) =
      omegaNode S (fun a => k (attachedNode D hS a)) b := by
  unfold omegaNode
  congr 1
  · exact (congrArg k (attachedNode_child D hS b 0)).symm
  · exact (congrArg k (attachedNode_child D hS b 1)).symm
  · exact (congrArg k (attachedNode_child D hS b 2)).symm
  · exact (chain_attachment_momentum D hS k hk b).symm

end WaveTurbulence.RegRed
