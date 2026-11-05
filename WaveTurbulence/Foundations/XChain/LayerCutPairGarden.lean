/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutBlockMaps
/-! Terminal inverse blocks give zero-order lower gardens entirely in layer p. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem cutBlockGarden_terminal_trees {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B)))
    (ht : ∀ b ∈ B, b.1.2 ∈ (LG.garden.tree b.1.1).leaves) (k : Fin B.card) :
    (cutBlockGarden LG p B hcp).garden.tree k = TTree.leaf :=
  (cutBlockGarden_tree LG p B hcp k).trans
    (subtreeAt_eq_leaf_of_mem_leaves _ (ht _ (B.equivFin.symm k).2))

theorem cutBlockGarden_terminal_layer {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (B : Finset (GLeaf (layerCutForest LG p)))
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B)))
    (ht : ∀ b ∈ B, b.1.2 ∈ (LG.garden.tree b.1.1).leaves ∧ LG.layer (cutLeafNodeEmbedding LG p b) = p)
    (a : GNode (cutBlockGarden LG p B hcp).garden.tree) : (cutBlockGarden LG p B hcp).layer a = p := by
  have ha := a.2
  rw [cutBlockGarden_terminal_trees LG p B hcp (fun b hb => (ht b hb).1) a.1.1,
    TTree.nodes, Finset.mem_singleton] at ha
  have he : cutBlockNodeMap LG p B hcp a = cutLeafNodeEmbedding LG p (B.equivFin.symm a.1.1).1 := by
    apply Subtype.ext
    exact (cutBlockNodeMap_val LG p B hcp a).trans (by simp only [ha, List.append_nil]; rfl)
  exact (cutBlockGarden_layer LG p B hcp a).trans
    ((congrArg LG.layer he).trans (ht _ (B.equivFin.symm a.1.1).2).2)

end WaveTurbulence.Induct
