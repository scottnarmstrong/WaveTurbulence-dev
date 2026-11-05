/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutBlockRoots
public import WaveTurbulence.Foundations.XChain.ExtractedCanonicalGarden
public import WaveTurbulence.Foundations.XChain.ReindexedCanonicalGarden
/-! The actual lower garden of an inverse top-leaf block, in its exact required enumeration. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def cutBlockGarden {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B))) : LayeredGarden B.card :=
  reindexLayeredGarden
    (extractedLayeredGarden LG (cutBlockRoots LG p B) (cutBlockRoots_antichain LG p B) hcp)
    (cutBlockRootIndexEquiv LG p B)

theorem cutBlockGarden_sig {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B))) (k : Fin B.card) :
    (cutBlockGarden LG p B hcp).garden.sig k =
      nodeSign LG.garden.sig (cutLeafNodeEmbedding LG p (B.equivFin.symm k).1).1 := by
  exact congrArg (fun u : GNode LG.garden.tree => nodeSign LG.garden.sig u.1)
    (cutBlockRootIndexEquiv_root LG p B k)

theorem cutBlockGarden_tree {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B))) (k : Fin B.card) :
    (cutBlockGarden LG p B hcp).garden.tree k =
      subtreeAt (LG.garden.tree (B.equivFin.symm k).1.1.1) (B.equivFin.symm k).1.1.2 := by
  exact congrArg (fun u : GNode LG.garden.tree => subtreeAt (LG.garden.tree u.1.1) u.1.2)
    (cutBlockRootIndexEquiv_root LG p B k)

theorem cutBlockGarden_isCanonG {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B)))
    (hcanon : LG.CanonInd p (cutBlockRoots LG p B)) : IsCanonG p (cutBlockGarden LG p B hcp) :=
  reindexLayeredGarden_isCanonG _ _
    (extracted_isCanonG_of_canonInd LG _ (cutBlockRoots_antichain LG p B) hcp p hcanon)

end WaveTurbulence.Induct
