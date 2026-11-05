/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.InverseGraftPairing
/-! Cutting, extracting the source components and regrafting restores the full layered garden. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem inverseGraft_layer_raw {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (a : GNode (inverseGraft LG p hbound hplain P hTD).garden.tree) (b : GNode LG.garden.tree)
    (hab : a.1 = b.1) : (inverseGraft LG p hbound hplain P hTD).layer a = LG.layer b := by
  obtain ⟨z, rfl⟩ := (gardenNodeEquiv (layerCutForest LG p) (layerCutPartition LG p hbound P)
    (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden)).surjective a
  rcases z with c | ⟨B, c⟩
  · have hc : layerCutNodeEmbedding LG p c.toNode = b :=
      Subtype.ext ((gardenNodeEquiv_top_val (layerCutForest LG p) (layerCutPartition LG p hbound P)
        (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden) c).symm.trans hab)
    have ht := graftLayer_top (layerCutForest LG p) (layerCutPartition LG p hbound P)
      (inverseLowerFamily LG p hbound hplain P hTD) p c
    exact ht.trans ((layerCut_branch_layer LG p hbound c).symm.trans (congrArg LG.layer hc))
  · have hc : cutBlockNodeMap LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B) c = b :=
      Subtype.ext ((inverseGraft_node_val LG p hbound hplain P hTD B c).symm.trans hab)
    have ht := graftLayer_lower (layerCutForest LG p) (layerCutPartition LG p hbound P)
      (inverseLowerFamily LG p hbound hplain P hTD) p B c
    have hl := cutBlockGarden_layer LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B) c
    exact ht.trans (hl.trans (congrArg LG.layer hc))

theorem inverseGraft_eq {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P) :
    inverseGraft LG p hbound hplain P hTD = LG :=
  layeredGarden_eq_of_raw_data _ _ (inverseGraft_garden LG p hbound hplain P hTD)
    (inverseGraft_layer_raw LG p hbound hplain P hTD)

end WaveTurbulence.Induct
