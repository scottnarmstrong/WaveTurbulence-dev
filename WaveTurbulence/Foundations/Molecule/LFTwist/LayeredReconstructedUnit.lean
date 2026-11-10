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

end WaveTurbulence.LFTwist
