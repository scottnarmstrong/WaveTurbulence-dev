/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutBlockGarden
/-! Literal original-node and original-leaf maps for each inverse lower block. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def cutBlockNodeMap {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B)))
    (a : GNode (cutBlockGarden LG p B hcp).garden.tree) : GNode LG.garden.tree :=
  subforestNodeMap (cutBlockRoots LG p B)
    (reindexNodeEquiv (subforestTrees (cutBlockRoots LG p B)) (cutBlockRootIndexEquiv LG p B) a)

noncomputable def cutBlockLeafMap {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B)))
    (ℓ : GLeaf (cutBlockGarden LG p B hcp).garden.tree) : GLeaf LG.garden.tree :=
  subforestLeafMap (cutBlockRoots LG p B)
    (reindexLeafEquiv (subforestTrees (cutBlockRoots LG p B)) (cutBlockRootIndexEquiv LG p B) ℓ)

theorem cutBlockNodeMap_val {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B)))
    (a : GNode (cutBlockGarden LG p B hcp).garden.tree) :
    (cutBlockNodeMap LG p B hcp a).1 =
      ((B.equivFin.symm a.1.1).1.1.1, (B.equivFin.symm a.1.1).1.1.2 ++ a.1.2) := by
  have he := cutBlockRootIndexEquiv_root LG p B a.1.1
  exact congrArg (fun u : GNode LG.garden.tree => (u.1.1, u.1.2 ++ a.1.2)) he

theorem cutBlockLeafMap_val {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B)))
    (ℓ : GLeaf (cutBlockGarden LG p B hcp).garden.tree) :
    (cutBlockLeafMap LG p B hcp ℓ).1 =
      ((B.equivFin.symm ℓ.1.1).1.1.1, (B.equivFin.symm ℓ.1.1).1.1.2 ++ ℓ.1.2) := by
  have he := cutBlockRootIndexEquiv_root LG p B ℓ.1.1
  exact congrArg (fun u : GNode LG.garden.tree => (u.1.1, u.1.2 ++ ℓ.1.2)) he

theorem cutBlockGarden_layer {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B)))
    (a : GNode (cutBlockGarden LG p B hcp).garden.tree) :
    (cutBlockGarden LG p B hcp).layer a = LG.layer (cutBlockNodeMap LG p B hcp a) := rfl

theorem cutBlockGarden_pair_map {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B)))
    (ℓ : GLeaf (cutBlockGarden LG p B hcp).garden.tree) :
    cutBlockLeafMap LG p B hcp ((cutBlockGarden LG p B hcp).garden.pair ℓ) =
      LG.garden.pair (cutBlockLeafMap LG p B hcp ℓ) := by
  have he := reindexGarden_pair_image
    (extractedGarden LG (cutBlockRoots LG p B) (cutBlockRoots_antichain LG p B) hcp)
    (cutBlockRootIndexEquiv LG p B) ℓ
  exact (congrArg (subforestLeafMap (cutBlockRoots LG p B)) he).trans
    (extractedGarden_pair_map LG _ (cutBlockRoots_antichain LG p B) hcp _)

end WaveTurbulence.Induct
