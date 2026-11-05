/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutLowerFamily
public import WaveTurbulence.Foundations.XChain.LayeredGraft
/-! The literal garden regrafted from the recovered top forest and lower component family. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem inverseLowerFamily_sig {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : ↥(layerCutPartition LG p hbound P).parts) (k : Fin B.1.card) :
    (inverseLowerFamily LG p hbound hplain P hTD B).garden.sig k =
      nodeSign LG.garden.sig ((blockRootEquiv (layerCutForest LG p) (layerCutPartition LG p hbound P)).symm ⟨B, k⟩).1 := by
  have hs := cutBlockGarden_sig LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B) k
  have he := congrArg (fun a : GLeaf (layerCutForest LG p) => nodeSign LG.garden.sig a.1)
    (blockRootEquiv_symm_eq (layerCutForest LG p) (layerCutPartition LG p hbound P) B k)
  exact hs.trans he.symm

noncomputable def inverseGraft {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P) : LayeredGarden w :=
  layeredGardenGraft LG.garden.sig (layerCutForest LG p) (layerCutPartition LG p hbound P)
    (inverseLowerFamily LG p hbound hplain P hTD) p
    (inverseLowerFamily_plain LG p hbound hplain P hTD)
    (inverseLowerFamily_sig LG p hbound hplain P hTD)
    (inverseLowerFamily_bound LG p hbound hplain P hTD)

theorem inverseLowerFamily_tree_at_leaf {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (a : GLeaf (layerCutForest LG p)) :
    blockGraftTrees (layerCutForest LG p) (layerCutPartition LG p hbound P)
      (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden) a.1.1 a.1.2 =
      subtreeAt (LG.garden.tree a.1.1) a.1.2 := by
  let z := blockRootEquiv (layerCutForest LG p) (layerCutPartition LG p hbound P) a
  have hb := blockGraftTrees_at_leaf (layerCutForest LG p) (layerCutPartition LG p hbound P)
    (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden) a
  have ht := cutBlockGarden_tree LG p z.1.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD z.1) z.2
  have he : (z.1.1.equivFin.symm z.2).1 = a :=
    (blockRootEquiv_symm_eq (layerCutForest LG p) (layerCutPartition LG p hbound P) z.1 z.2).symm.trans
      ((blockRootEquiv (layerCutForest LG p) (layerCutPartition LG p hbound P)).symm_apply_apply a)
  have hv := congrArg (fun a : GLeaf (layerCutForest LG p) => subtreeAt (LG.garden.tree a.1.1) a.1.2) he
  exact hb.trans (ht.trans hv)

theorem inverseGraft_tree {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P) :
    (inverseGraft LG p hbound hplain P hTD).garden.tree = LG.garden.tree := by
  have he : (inverseGraft LG p hbound hplain P hTD).garden.tree =
      graftForest (layerCutForest LG p) (fun j => subtreeAt (LG.garden.tree j)) := by
    funext j
    apply graftTree_congr
    intro a ha
    exact inverseLowerFamily_tree_at_leaf LG p hbound hplain P hTD ⟨(j, a), ha⟩
  exact he.trans (layerCutForest_graft_reconstruct LG p)

end WaveTurbulence.Induct
