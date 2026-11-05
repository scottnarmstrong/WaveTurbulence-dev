/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.InverseGraft
/-! Original addresses of all lower nodes and leaves in the inverse regraft. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem inverseGraft_leaf_val {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : ↥(layerCutPartition LG p hbound P).parts)
    (ℓ : GLeaf (inverseLowerFamily LG p hbound hplain P hTD B).garden.tree) :
    ((gardenLeafEquiv (layerCutForest LG p) (layerCutPartition LG p hbound P)
      (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden)).symm ⟨B, ℓ⟩).1 =
      (cutBlockLeafMap LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B) ℓ).1 := by
  have hg := gardenLeafEquiv_symm_val (layerCutForest LG p) (layerCutPartition LG p hbound P)
    (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden) B ℓ
  have hr := blockRootEquiv_symm_eq (layerCutForest LG p) (layerCutPartition LG p hbound P) B ℓ.1.1
  have he := congrArg (fun a : GLeaf (layerCutForest LG p) => (a.1.1, a.1.2 ++ ℓ.1.2)) hr
  have hl := cutBlockLeafMap_val LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B) ℓ
  exact hg.trans (he.trans hl.symm)

theorem inverseGraft_node_val {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : ↥(layerCutPartition LG p hbound P).parts)
    (a : GNode (inverseLowerFamily LG p hbound hplain P hTD B).garden.tree) :
    (gardenNodeEquiv (layerCutForest LG p) (layerCutPartition LG p hbound P)
      (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden) (.inr ⟨B, a⟩)).1 =
      (cutBlockNodeMap LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B) a).1 := by
  have hg := gardenNodeEquiv_lower_val (layerCutForest LG p) (layerCutPartition LG p hbound P)
    (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden) B a
  have hr := blockRootEquiv_symm_eq (layerCutForest LG p) (layerCutPartition LG p hbound P) B a.1.1
  have he := congrArg (fun l : GLeaf (layerCutForest LG p) => (l.1.1, l.1.2 ++ a.1.2)) hr
  have hl := cutBlockNodeMap_val LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B) a
  exact hg.trans (he.trans hl.symm)

end WaveTurbulence.Induct
