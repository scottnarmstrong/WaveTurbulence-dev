/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.NativeTopCounts
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence

/-! # Native layer counts in any actual decoded layered carrier -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton RegRed Links
variable {w : ℕ} {S : Garden w}

@[expose] noncomputable def rawCoreTopCount (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (p : ℕ) (j : Fin w) : ℕ :=
  ∑ b : GBranch S.tree, if (D.coreBranch hS b).1.1 = j ∧ layerAt LG (D.corePosition b) = p then 1 else 0

@[expose] noncomputable def rawTreeTopCount (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (p : ℕ) (b : GBranch S.tree) (j : Fin w) : ℕ :=
  ∑ c : ChainBranchPath D b, if (chainContextBranch D hS b c).1.1 = j ∧
    layerAt LG (chainContextBranch D hS b c).1 = p then 1 else 0

@[expose] noncomputable def rawCoupleTopCount (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (p : ℕ) (q : SourcePair S) (j : Fin w) : ℕ :=
  ∑ c : GBranch (decodedCouple (D.couple q)).tree,
    if (coupleContextBranch D hS q c).1.1 = j ∧ layerAt LG (coupleContextBranch D hS q c).1 = p then 1 else 0

@[expose] noncomputable def rawTreeLayerCount (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (p : ℕ) (b : GBranch S.tree) : ℕ :=
  ∑ c : ChainBranchPath D b, if layerAt LG (chainContextBranch D hS b c).1 = p then 1 else 0

@[expose] noncomputable def rawCoupleLayerCount (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (p : ℕ) (q : SourcePair S) : ℕ :=
  ∑ c : GBranch (decodedCouple (D.couple q)).tree,
    if layerAt LG (coupleContextBranch D hS q c).1 = p then 1 else 0

/-- Every actual branch is counted once: core, couple, or regular-tree interior. -/
theorem raw_topOrder_split (LG : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS LG.garden) (p : ℕ) (j : Fin w) :
    LG.topOrder p j = rawCoreTopCount LG D hS p j +
      (∑ q, rawCoupleTopCount LG D hS p q j) + ∑ b, rawTreeTopCount LG D hS p b j := by
  rcases LG with ⟨G,layer,hLayer⟩
  have he : G = D.garden hS := rawOfGarden_injective_plain hd.1 (D.garden_plain hS)
    (hd.2.symm.trans (D.garden_raw hS).symm)
  subst G
  have hc (b : GBranch S.tree) :
      layerAt (layeredReconstruction D hS layer hLayer) (D.corePosition b) = layer (D.coreBranch hS b).toNode :=
    layerAt_node (layeredReconstruction D hS layer hLayer) (D.coreBranch hS b).toNode
  have ht (b : GBranch S.tree) (c : ChainBranchPath D b) :
      layerAt (layeredReconstruction D hS layer hLayer) (chainContextBranch D hS b c).1 =
        layer (chainContextBranch D hS b c).toNode := layerAt_node (layeredReconstruction D hS layer hLayer) (chainContextBranch D hS b c).toNode
  have hq (q : SourcePair S) (c : GBranch (decodedCouple (D.couple q)).tree) :
      layerAt (layeredReconstruction D hS layer hLayer) (coupleContextBranch D hS q c).1 =
        layer (coupleContextBranch D hS q c).toNode := layerAt_node (layeredReconstruction D hS layer hLayer) (coupleContextBranch D hS q c).toNode
  change (layeredReconstruction D hS layer hLayer).topOrder p j =
    rawCoreTopCount (layeredReconstruction D hS layer hLayer) D hS p j +
      (∑ q, rawCoupleTopCount (layeredReconstruction D hS layer hLayer) D hS p q j) +
      ∑ b, rawTreeTopCount (layeredReconstruction D hS layer hLayer) D hS p b j
  simpa only [rawCoreTopCount,rawCoupleTopCount,rawTreeTopCount,hc,ht,hq,
    coreTopCount,coupleTopCount,treeTopCount] using reconstructed_topOrder_split D hS layer p hLayer j

end WaveTurbulence.LFTwist
