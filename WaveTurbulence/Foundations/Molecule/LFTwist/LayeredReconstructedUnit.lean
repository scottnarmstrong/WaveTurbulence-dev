/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructedUnitGarden
public import WaveTurbulence.Foundations.Molecule.LFTwist.SourceExpandedUnit
public import WaveTurbulence.Foundations.Molecule.LFTwist.ChainNodeTransport

/-! # Actual layered reconstruction of the erased unit twist -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links RegRed
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

@[expose] noncomputable def erasedUnitLayered
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)
    (he : SameLowerLayer (layeredReconstruction D hS layer hLayer)
      (expandedPlacement D hS (D.garden_decodes hS) P hq)) : LayeredGarden w :=
  unitLayerTwist (layeredReconstruction D hS layer hLayer)
    (expandedPlacement D hS (D.garden_decodes hS) P hq) he

/-- The constructed layered unit has the entire literal transported reconstruction. -/
theorem erasedUnit_decodes (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)
    (he : SameLowerLayer (layeredReconstruction D hS layer hLayer)
      (expandedPlacement D hS (D.garden_decodes hS) P hq)) :
    (twistReconstruction S P hS D).Decodes (unitTwistGarden_plain S P hS)
      (erasedUnitLayered S P hS D layer hLayer hq he).garden := by
  have hg : (twistReconstruction S P hS D).garden (unitTwistGarden_plain S P hS) =
      (erasedUnitLayered S P hS D layer hLayer hq he).garden :=
    reconstructed_unit_garden S P hS D hnil hq
  exact Eq.mp (congrArg ((twistReconstruction S P hS D).Decodes (unitTwistGarden_plain S P hS)) hg)
    ((twistReconstruction S P hS D).garden_decodes (unitTwistGarden_plain S P hS))

/-- Every actual node retains its layer under the physical exchange. -/
theorem erasedUnit_layerAt (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)
    (he : SameLowerLayer (layeredReconstruction D hS layer hLayer)
      (expandedPlacement D hS (D.garden_decodes hS) P hq)) (n : GNode (D.forest hS)) :
    layerAt (erasedUnitLayered S P hS D layer hLayer hq he) (inflatedExchange S P D n.1) = layer n := by
  let G := D.garden hS
  let Q := expandedPlacement D hS (D.garden_decodes hS) P hq
  have ha : Q.lower.1 = inflatedPosition S D.tree P.lower.toNode := by
    change addrExt (inflatedPosition S D.tree P.lower.toNode) (D.tree P.lower).lonePath = _
    simp only [hnil, RegChain.lonePath, addrExt_nil]
  have hb : (G.pair Q.retained).1 = inflatedPosition S D.tree (S.pair P.retained).toNode :=
    congrArg Subtype.val (decodedTrivLeaf_pair D hS (D.garden_decodes hS) P.retained hq)
  have hv : (naiveNodeEquiv G Q n).1 = inflatedExchange S P D n.1 :=
    (naiveNodeEquiv_address G Q n).trans (by rw [ha,hb]; rfl)
  exact (congrArg (layerAt (erasedUnitLayered S P hS D layer hLayer hq he)) hv.symm).trans
    ((layerAt_node (erasedUnitLayered S P hS D layer hLayer hq he) (naiveNodeEquiv G Q n)).trans
      (unitLayerTwist_node (layeredReconstruction D hS layer hLayer) Q he n))

/-- Every ordinary regular-tree node, including its lone leaf, has the same
layer in the actual transported reconstruction. -/
theorem erasedUnit_ordinary_tree_layer (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)
    (he : SameLowerLayer (layeredReconstruction D hS layer hLayer)
      (expandedPlacement D hS (D.garden_decodes hS) P hq))
    (b : GBranch S.tree) (hb : b ≠ P.lower)
    (n : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) :
    layerAt (erasedUnitLayered S P hS D layer hLayer hq he)
      (addrExt (inflatedPosition (unitTwistGarden S P) (twistReconstruction S P hS D).tree
        (coreBranchEquiv S P b).toNode) n.1.2) = layer (chainContextNode D hS b n) := by
  have hv := ordinary_chain_node_address_twist S D P hS hnil b hb n.1.2 n.2
  exact (congrArg (layerAt (erasedUnitLayered S P hS D layer hLayer hq he)) hv).trans
    (erasedUnit_layerAt S P hS D layer hLayer hnil hq he (chainContextNode D hS b n))

/-- Literal node inside the replacement tree at a source leaf. -/
@[expose] noncomputable def leafContextNode (l : GLeaf S.tree) (q : Path)
    (hq : q ∈ (D.leafTree hS l).nodes) : GNode (D.forest hS) :=
  ⟨addrExt (inflatedPosition S D.tree l.toNode) q, by
    have hs := (D.forest_subtree_position hS l.toNode).trans
      (congrArg some (D.inflateNode_leaf hS l))
    exact (Comb.subtree_nodes_iff hs q).mp hq⟩

/-- Each ordinary couple's two rooted replacement trees keep every node layer.
The actual oriented endpoint correspondence is supplied by twistSourcePair_sides. -/
theorem erasedUnit_ordinary_leaf_tree_layer (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)
    (he : SameLowerLayer (layeredReconstruction D hS layer hLayer)
      (expandedPlacement D hS (D.garden_decodes hS) P hq))
    (l : GLeaf S.tree) (hl : l ≠ S.pair P.retained) (q : Path)
    (hp : q ∈ (D.leafTree hS l).nodes) :
    layerAt (erasedUnitLayered S P hS D layer hLayer hq he)
      (addrExt (inflatedPosition (unitTwistGarden S P) (twistReconstruction S P hS D).tree
        (coreLeafEquiv S P l).toNode) q) = layer (leafContextNode S hS D l q hp) := by
  have hv := congrArg (fun a => addrExt a q) (inflatedPosition_leaf_twist S P hS D hnil l)
  have heq := ((inflatedExchange_leaf_respectsAt S P D l hl) q).symm
  exact (congrArg (layerAt (erasedUnitLayered S P hS D layer hLayer hq he)) (hv.trans heq)).trans
    (erasedUnit_layerAt S P hS D layer hLayer hnil hq he (leafContextNode S hS D l q hp))

end WaveTurbulence.LFTwist
