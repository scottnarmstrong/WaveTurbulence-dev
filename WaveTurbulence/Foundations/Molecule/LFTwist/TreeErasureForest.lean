/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.RestoreForest
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsePairedTreeGarden
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeRawFactorization
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionChainBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden

/-! # Actual paired-tree collapse erases exactly its reconstruction forest slot -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton

private theorem restore_forest_of_eq {w : ℕ} (tree base : Fin w → TTree)
    (a : GNode base) (s : TTree) (a' : GNode tree)
    (he : tree = Comb.replaceNodeForest base a s) (ha : a'.1 = a.1) :
    Comb.replaceNodeForest tree a' (Comb.nodeSubtree a) = base := by
  subst tree
  exact replaceNodeForest_restore base a s a' ha

/-- No bare-chain restriction: collapse removes a general regular tree with
all its nested regular couples, leaving the exact erased reconstruction forest. -/
theorem eraseTree_collapse_forest {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) :
    (collapsePairedTreeGarden
      (D.decoded_chain_isSubPairedTree hS (D.garden_decodes hS) b)).tree = (D.eraseTree b).forest hS := by
  let E := D.eraseTree b
  let a₀ := E.decodedNode hS (E.garden_decodes hS) b.toNode
  let a₁ := D.decodedNode hS (D.garden_decodes hS) b.toNode
  let c₁ := D.decodedCoreNode hS (D.garden_decodes hS) b
  let A := inflatedPosition S E.tree b.toNode
  let t := (D.tree b).plug (nodeSign S.sig A) ((E.forest hS A.1).subtreeAt A.2)
  have hF : D.forest hS = Comb.replaceNodeForest (E.forest hS) a₀ t := by
    have hh := D.eraseTree_raw_forest hS b
    change D.forest hS = Function.update (E.forest hS) A.1
      ((E.forest hS A.1).setAt A.2 t) at hh
    change D.forest hS = Function.update (E.forest hS) A.1
      (Comb.replaceAt (E.forest hS A.1) A.2 t)
    simpa only [setAt_eq_replaceAt] using hh
  have ha : a₁.1 = a₀.1 := (D.eraseTree_position_at b).symm
  have h₀ : Comb.nodeSubtree a₀ = E.inflateNode hS b.toNode :=
    Option.some.inj ((Comb.nodeSubtree_spec a₀).symm.trans (E.forest_subtree_position hS b.toNode))
  have h₁ : Comb.nodeSubtree c₁ = node3 (fun i => D.inflateNode hS (b.child i)) :=
    Option.some.inj ((Comb.nodeSubtree_spec c₁).symm.trans
      (D.decoded_subtree_core hS (D.garden_decodes hS) b))
  have hc : Comb.nodeSubtree c₁ = Comb.nodeSubtree a₀ :=
    h₁.trans ((D.eraseTree_inflateNode_at hS b).symm.trans h₀.symm)
  change Comb.replaceNodeForest (D.forest hS) a₁ (Comb.nodeSubtree c₁) = E.forest hS
  exact (congrArg (Comb.replaceNodeForest (D.forest hS) a₁) hc).trans
    (restore_forest_of_eq (D.forest hS) (E.forest hS) a₀ t a₁ hF ha)

end WaveTurbulence.LFTwist
