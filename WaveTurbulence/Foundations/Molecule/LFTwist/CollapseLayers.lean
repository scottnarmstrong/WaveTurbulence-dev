/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.BranchLayering
public import WaveTurbulence.Foundations.Molecule.LFTwist.StretchOrder
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsePairedTreeNodes
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseCoupleNodes

/-! # Actual layered collapses of the two LF attachment kinds

Paired-tree collapse pulls back all node layers through the prefix embedding.
Couple collapse retains branch layers and assigns minimum-parent layers to the
new paired leaves. These are actual gardens, with no canonical-output premise.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton
variable {w : ℕ}

/-- The surviving paired-tree nodes inherit an actual layering. -/
theorem collapsePairedTree_isLayering (LG : LayeredGarden w)
    {a b : GNode LG.garden.tree} (h : Comb.IsSubPairedTree LG.garden a b) :
    IsLayering (collapsePairedTreeGarden h)
      (fun n => LG.layer (collapsePairedTreeNodeEmbedding h n)) := by
  constructor
  · intro c i
    apply LG.layer_le_of_isDesc
    have hr : Below c.toNode.1 (c.child i).1 := by
      exact ⟨rfl, List.prefix_append _ _⟩
    have hs := stretch_below_mono a.1 (Comb.collapseDataOfDesc h.1).path hr
    exact ⟨hs.1.symm, hs.2⟩
  · intro l
    have he := collapsePairedTreeGarden_pair h l
    have hL := LG.isLayering.2 (pairedTreeLeafEmbedding h l)
    change LG.layer (pairedTreeLeafEmbedding h l).toNode =
      LG.layer (pairedTreeLeafEmbedding h ((collapsePairedTreeGarden h).pair l)).toNode
    rw [he]
    exact hL

/-- The literal paired-tree collapse with inherited layers. -/
@[expose] noncomputable def collapsePairedTreeLayered (LG : LayeredGarden w)
    {a b : GNode LG.garden.tree} (h : Comb.IsSubPairedTree LG.garden a b) : LayeredGarden w :=
  ⟨collapsePairedTreeGarden h, (fun n => LG.layer (collapsePairedTreeNodeEmbedding h n)),
    collapsePairedTree_isLayering LG h⟩

/-- Surviving couple-collapse branches inherit a monotone pre-layering. -/
theorem collapseCouple_branchPrelayering (LG : LayeredGarden w)
    {a b : GNode LG.garden.tree} (h : Comb.IsSubCouple LG.garden a b) :
    IsBranchPrelayering (collapseCoupleGarden h)
      (fun c => LG.layer (collapseCoupleBranchEmbedding h c).toNode) := by
  intro c d i hd
  apply LG.layer_le_of_isDesc
  have he := congrArg (fun n : GNode (collapseCoupleGarden h).tree => n.1) hd
  change c.1.1 = d.1.1 ∧ c.1.2 <+: d.1.2
  change d.1 = (c.1.1, c.1.2 ++ [i]) at he
  exact ⟨(congrArg Prod.fst he).symm,
    (congrArg Prod.snd he).symm ▸ List.prefix_append _ _⟩

/-- The actual couple collapse, with the source minimum-parent extension. -/
@[expose] noncomputable def collapseCoupleLayered (LG : LayeredGarden w)
    {a b : GNode LG.garden.tree} (h : Comb.IsSubCouple LG.garden a b) (p : ℕ) : LayeredGarden w :=
  branchLayeredGarden (collapseCoupleGarden h)
    (fun c => LG.layer (collapseCoupleBranchEmbedding h c).toNode) p
    (collapseCouple_branchPrelayering LG h)

/-- Couple collapse preserves exactly every surviving branching-node layer. -/
theorem collapseCoupleLayered_branch (LG : LayeredGarden w)
    {a b : GNode LG.garden.tree} (h : Comb.IsSubCouple LG.garden a b) (p : ℕ)
    (c : GBranch (collapseCoupleGarden h).tree) :
    (collapseCoupleLayered LG h p).layer c.toNode =
      LG.layer (collapseCoupleBranchEmbedding h c).toNode :=
  extendBranchLayers_branch _ _ _ _

end WaveTurbulence.LFTwist
