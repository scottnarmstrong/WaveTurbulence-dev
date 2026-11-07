/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD10
public import WaveTurbulence.Foundations.Stage1.Represents.RepVE3
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: the leaf-size bookkeeping of the vine pieces

`leaf_prod_split`: for a constant leaf bound `β`, the leaf size of the reconstruction is the product of the outer slot leaf sizes
and the regional leaf sizes of the units.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS5C

variable {w : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

theorem leaf_prod_split (Φ : SpliceShape blk Gsb) (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain)
    (hSb : Gsb.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (β : NNReal) :
    (∏ s', slotLeaf D hS layer hLayer (fun _ => β) (Φ.iota hS hSb s')) *
        ∏ j, regionLeafSize D hS (regionOf (blk j)) layer hLayer (fun _ => (β : ℝ)) =
      leafSizeProduct (layeredReconstruction D hS layer hLayer) (fun _ => β) := by
  rw [← prod_slotLeaf D hS layer hLayer (fun _ => β)]
  have h1 := prod_slots (blk := blk) hS hd (M := ℝ) (slotLeaf D hS layer hLayer (fun _ => β))
  rw [h1, ← Φ.prod_outer_iota hS hSb (M := ℝ) (slotLeaf D hS layer hLayer (fun _ => β))]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [prod_regSlots (blk := blk) hS j (M := ℝ) (slotLeaf D hS layer hLayer (fun _ => β))]
  unfold regionLeafSize slotLeaf leafSizeProduct
  congr 1
  · refine Finset.prod_congr rfl fun p' _ => ?_
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    have hn : ℓ.1.2 ∈ ((nativeCoupleGarden D hS p').tree ℓ.1.1).nodes := ℓ.toNode.2
    simp only [nativeCoupleB, hn, ↓reduceDIte]
  · refine Finset.prod_congr rfl fun v _ => ?_
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    have hn : ℓ.1.2 ∈ ((decodedTree (D.tree v) (nodeSign S.sig v.1)).tree ℓ.1.1).nodes := ℓ.toNode.2
    simp only [nativeChainB, hn, ↓reduceDIte]

end WaveTurbulence.Represents
