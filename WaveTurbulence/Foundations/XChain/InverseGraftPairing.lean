/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.InverseGraftAddresses
public import WaveTurbulence.Foundations.XChain.GardenDataExt
/-! The inverse regraft restores the original pairing and the entire concrete garden. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem inverseGraft_pair_lower_raw {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : ↥(layerCutPartition LG p hbound P).parts)
    (ℓ : GLeaf (inverseLowerFamily LG p hbound hplain P hTD B).garden.tree) :
    ((inverseGraft LG p hbound hplain P hTD).garden.pair
      ((gardenLeafEquiv (layerCutForest LG p) (layerCutPartition LG p hbound P)
        (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden)).symm ⟨B, ℓ⟩)).1 =
      (LG.garden.pair (cutBlockLeafMap LG p B.1
        (layerCut_block_completelyPaired LG p hbound hplain P hTD B) ℓ)).1 := by
  have hp := gardenGraft_pair_lower LG.garden.sig (layerCutForest LG p) (layerCutPartition LG p hbound P)
    (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden)
    (inverseLowerFamily_plain LG p hbound hplain P hTD) (inverseLowerFamily_sig LG p hbound hplain P hTD) B ℓ
  have hp' := congrArg (fun l : GLeaf (inverseGraft LG p hbound hplain P hTD).garden.tree => l.1) hp
  have hv := inverseGraft_leaf_val LG p hbound hplain P hTD B
    ((inverseLowerFamily LG p hbound hplain P hTD B).garden.pair ℓ)
  have hs := congrArg (fun l : GLeaf LG.garden.tree => l.1)
    (cutBlockGarden_pair_map LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B) ℓ)
  exact hp'.trans (hv.trans hs)

theorem inverseGraft_pair_raw {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (a : GLeaf (inverseGraft LG p hbound hplain P hTD).garden.tree) (b : GLeaf LG.garden.tree)
    (hab : a.1 = b.1) :
    ((inverseGraft LG p hbound hplain P hTD).garden.pair a).1 = (LG.garden.pair b).1 := by
  obtain ⟨⟨B, l⟩, rfl⟩ := (gardenLeafEquiv (layerCutForest LG p) (layerCutPartition LG p hbound P)
    (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden)).symm.surjective a
  have he : cutBlockLeafMap LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B) l = b :=
    Subtype.ext ((inverseGraft_leaf_val LG p hbound hplain P hTD B l).symm.trans hab)
  exact (inverseGraft_pair_lower_raw LG p hbound hplain P hTD B l).trans
    (congrArg (fun l : GLeaf LG.garden.tree => (LG.garden.pair l).1) he)

theorem inverseGraft_garden {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P) :
    (inverseGraft LG p hbound hplain P hTD).garden = LG.garden := by
  apply garden_eq_of_raw_data
  · rfl
  · exact inverseGraft_tree LG p hbound hplain P hTD
  · exact inverseGraft_pair_raw LG p hbound hplain P hTD
  · intro a b _
    exact (hplain b).symm

end WaveTurbulence.Induct
