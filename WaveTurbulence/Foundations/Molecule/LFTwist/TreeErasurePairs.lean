/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.PairEmbedding
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeRawFactorization
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden

/-! # Every surviving erased-tree pair is an actual original background pair -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton

/-- General regular-tree insertion retains the entire actual outside matching,
including arbitrary nested regular couples in every other replacement slot. -/
theorem eraseTree_background_pair_inclusion {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) (q : Pair w)
    (hq : q ∈ sourcePairs ((D.eraseTree b).garden hS)) :
    mapPairAddresses
      (stretch (inflatedPosition S (D.eraseTree b).tree b.toNode) (D.tree b).lonePath) q ∈
        sourcePairs (D.garden hS) := by
  have hE := congrArg Raw.pairs ((D.eraseTree b).garden_raw hS)
  have hD := congrArg Raw.pairs (D.garden_raw hS)
  change sourcePairs ((D.eraseTree b).garden hS) = ((D.eraseTree b).raw hS).pairs at hE
  change sourcePairs (D.garden hS) = (D.raw hS).pairs at hD
  rw [hE] at hq
  rw [hD, D.eraseTree_raw_pairs hS b]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)

end WaveTurbulence.LFTwist
