/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ExtractedGardenPair
public import WaveTurbulence.Foundations.XChain.ExtractedSubforestNodes
/-! The actual layered garden induced by a completely paired antichain subforest. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def extractedLayeredGarden {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) : LayeredGarden U.card where
  garden := extractedGarden LG U hU hcp
  layer := fun a => LG.layer (subforestNodeMap U a)
  isLayering := by
    constructor
    · intro b i
      have he := congrArg LG.layer (subforestBranchMap_child U b i)
      exact he.symm.le.trans (LG.isLayering.1 (subforestBranchMap U b) i)
    · intro ℓ
      have he := congrArg (fun l : GLeaf LG.garden.tree => LG.layer l.toNode)
        (extractedPair_image LG U hU hcp ℓ)
      exact (LG.isLayering.2 (subforestLeafMap U ℓ)).trans he.symm

theorem extractedLayeredGarden_isPlain {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) :
    (extractedLayeredGarden LG U hU hcp).garden.IsPlain := fun _ => rfl

theorem subforestNodeMap_root {w : ℕ} {tree : Fin w → TTree}
    (U : Finset (GNode tree)) (k : Fin U.card) :
    subforestNodeMap U (GNode.root (subforestTrees U) k) = subforestRoot U k := by
  apply Subtype.ext
  exact Prod.ext rfl (List.append_nil _)

end WaveTurbulence.Induct
