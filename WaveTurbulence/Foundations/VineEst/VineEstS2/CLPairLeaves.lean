/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInternalLeaves
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLStarConsumption

/-! # The two actual cropped leaves of each regional source pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable def clPairFirstLeaf (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) : GLeaf (CLTreeForest R) :=
  Classical.choose (clInternalLeaf_surjective hU R (p.1.firstLeaf hG)
    ((leaf_mem_clRealizationNodes _).mp (clRegionalPair_realization hG p.1 p.2).1))

noncomputable def clPairSecondLeaf (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) : GLeaf (CLTreeForest R) :=
  Classical.choose (clInternalLeaf_surjective hU R (p.1.secondLeaf hG)
    ((leaf_mem_clRealizationNodes _).mp (clRegionalPair_realization hG p.1 p.2).2))

theorem clPairFirstLeaf_node (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) :
    clTreeNode R (clPairFirstLeaf hU R hG p).toNode = (p.1.firstLeaf hG).toNode :=
  Classical.choose_spec (clInternalLeaf_surjective hU R (p.1.firstLeaf hG)
    ((leaf_mem_clRealizationNodes _).mp (clRegionalPair_realization hG p.1 p.2).1))

theorem clPairSecondLeaf_node (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) :
    clTreeNode R (clPairSecondLeaf hU R hG p).toNode = (p.1.secondLeaf hG).toNode :=
  Classical.choose_spec (clInternalLeaf_surjective hU R (p.1.secondLeaf hG)
    ((leaf_mem_clRealizationNodes _).mp (clRegionalPair_realization hG p.1 p.2).2))

theorem clPairFirstLeaf_sign (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) :
    nodeSign (fun _ : Fin 1 => G.sign a.toNode) (clPairFirstLeaf hU R hG p).1 = 1 := by
  calc
    _ = G.sign (clTreeNode R (clPairFirstLeaf hU R hG p).toNode) := (clTreeNode_sign R _).symm
    _ = G.sign (p.1.firstLeaf hG).toNode := congrArg G.sign (clPairFirstLeaf_node hU R hG p)
    _ = 1 := sourcePair_first_sign G hG p.1

theorem clPairSecondLeaf_sign (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) :
    nodeSign (fun _ : Fin 1 => G.sign a.toNode) (clPairSecondLeaf hU R hG p).1 = -1 := by
  calc
    _ = G.sign (clTreeNode R (clPairSecondLeaf hU R hG p).toNode) := (clTreeNode_sign R _).symm
    _ = G.sign (p.1.secondLeaf hG).toNode := congrArg G.sign (clPairSecondLeaf_node hU R hG p)
    _ = -1 := sourcePair_second_sign G hG p.1

end WaveTurbulence.VineEstS2
