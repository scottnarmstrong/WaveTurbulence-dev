/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.TreeErasureLinks
public import WaveTurbulence.Foundations.Molecule.LFTwist.CoherentErasure
public import WaveTurbulence.Foundations.Molecule.LFTwist.Prelayering
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeCoreTransport

/-! # Erasing one tree preserves every other coherence condition and core layer -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

theorem decoded_reconstruction_collapse_path {w : ℕ} {S G : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS G) (b : GBranch S.tree) :
    (Comb.collapseDataOfDesc (D.decoded_chain_isSubPairedTree hS hd b).1).path = (D.tree b).lonePath := by
  have he := collapseData_frame (D.decoded_chain_isSubPairedTree hS hd b).1
  have hp := congrArg (fun z : Address w => z.2) he
  change (inflatedPosition S D.tree b.toNode).2 ++ (D.tree b).lonePath =
    (inflatedPosition S D.tree b.toNode).2 ++ _ at hp
  exact (List.append_cancel_left hp).symm

/-- Pullback agrees at every raw address, including the zero convention away from nodes. -/
theorem treeCollapse_layerAt_stretch {w : ℕ} (LG : LayeredGarden w)
    {a b : GNode LG.garden.tree} (h : Comb.IsSubPairedTree LG.garden a b) (z : Address w) :
    layerAt LG (stretch a.1 (Comb.collapseDataOfDesc h.1).path z) =
      layerAt (collapsePairedTreeLayered LG h) z := by
  have hz : ¬ InTree a.1 b.1 (stretch a.1 (Comb.collapseDataOfDesc h.1).path z) := by
    simpa only [← collapseData_frame h.1] using
      stretch_outside_tree_interval a.1 z (Comb.collapseDataOfDesc h.1).path
  have he : shiftAddr b.1 a.1 (stretch a.1 (Comb.collapseDataOfDesc h.1).path z) = z := by
    simpa only [← collapseData_frame h.1] using shift_stretch_collapse a.1 z (Comb.collapseDataOfDesc h.1).path
  exact ((collapsePairedTree_outAgree LG h).layer _ hz).trans
    (congrArg (layerAt (collapsePairedTreeLayered LG h)) he)

/-- The exact prefix in the erased assignment is the exact raw layer pullback map. -/
theorem eraseTree_native_layerAt {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    (b : GBranch S.tree) (z : Address w) :
    layerAt LG (stretch (inflatedPosition S (D.eraseTree b).tree b.toNode) (D.tree b).lonePath z) =
      layerAt (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)) z := by
  have he := treeCollapse_layerAt_stretch LG (D.decoded_chain_isSubPairedTree hS hd b) z
  change layerAt LG (stretch (inflatedPosition S D.tree b.toNode)
    (Comb.collapseDataOfDesc (D.decoded_chain_isSubPairedTree hS hd b).1).path z) = _ at he
  rw [decoded_reconstruction_collapse_path D hS hd b, ← D.eraseTree_position_at b] at he
  exact he

/-- The actual induced branch pre-layering is unchanged by coherent-tree erasure. -/
theorem eraseTree_inducedPrelayer_eq {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (b : GBranch S.tree) :
    inducedPrelayer (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b))
      (D.eraseTree b) hS (eraseTree_collapse_decodes D hS hd b) = inducedPrelayer LG D hS hd := by
  funext c
  change LG.layer (collapsePairedTreeNodeEmbedding (D.decoded_chain_isSubPairedTree hS hd b)
    ((D.eraseTree b).decodedCoreBranch hS (eraseTree_collapse_decodes D hS hd b) c).toNode) =
      LG.layer (D.decodedCoreBranch hS hd c).toNode
  apply congrArg LG.layer
  apply Subtype.ext
  change stretch (inflatedPosition S D.tree b.toNode)
    (Comb.collapseDataOfDesc (D.decoded_chain_isSubPairedTree hS hd b).1).path
      ((D.eraseTree b).corePosition c) = D.corePosition c
  rw [decoded_reconstruction_collapse_path D hS hd b, ← D.eraseTree_position_at b]
  exact (D.eraseTree_corePosition b c).symm

end WaveTurbulence.LFTwist
