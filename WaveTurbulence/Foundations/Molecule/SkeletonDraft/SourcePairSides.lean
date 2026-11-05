/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairPayload

/-! # Exact sign sides and shared couple codes at canonical source leaf-pair slots -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem pairOfLeaf_firstLeaf {w : ℕ} (S : Garden w) (hS : S.IsPlain) (p : SourcePair S) :
    pairOfLeaf S hS (p.firstLeaf hS) = p :=
  Subtype.ext (sourcePairAt_sourcePairLeaf S hS p 0)

theorem pairOfLeaf_secondLeaf {w : ℕ} (S : Garden w) (hS : S.IsPlain) (p : SourcePair S) :
    pairOfLeaf S hS (p.secondLeaf hS) = p :=
  Subtype.ext (sourcePairAt_sourcePairLeaf S hS p 1)

theorem sourcePair_first_sign {w : ℕ} (S : Garden w) (hS : S.IsPlain) (p : SourcePair S) :
    nodeSign S.sig (p.firstLeaf hS).1 = 1 :=
  ((rawOfGarden_valid S hS).1 p.1 p.2).2.2.1

theorem sourcePair_second_sign {w : ℕ} (S : Garden w) (hS : S.IsPlain) (p : SourcePair S) :
    nodeSign S.sig (p.secondLeaf hS).1 = -1 :=
  ((rawOfGarden_valid S hS).1 p.1 p.2).2.2.2

theorem ReconstructionData.leafTree_first {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) : D.leafTree hS (p.firstLeaf hS) = (D.couple p).trees.1 := by
  rw [ReconstructionData.leafTree,pairOfLeaf_firstLeaf,sourcePair_first_sign]
  exact ite_eq_left rfl

theorem ReconstructionData.leafTree_second {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) : D.leafTree hS (p.secondLeaf hS) = (D.couple p).trees.2 := by
  rw [ReconstructionData.leafTree,pairOfLeaf_secondLeaf,sourcePair_second_sign]
  exact ite_eq_right (by decide : (-1 : ℤˣ) ≠ 1)

end WaveTurbulence.Reg.Skeleton
