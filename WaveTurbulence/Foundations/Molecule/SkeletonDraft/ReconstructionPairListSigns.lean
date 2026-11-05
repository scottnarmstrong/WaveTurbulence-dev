/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairListMembership
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairSides
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSigns

/-! # Every literal reconstruction pair has its prescribed positive-negative orientation -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.pairList_signs {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (q : Pair w) (hq : q ∈ D.pairList hS) :
    nodeSign S.sig q.1 = 1 ∧ nodeSign S.sig q.2 = -1 := by
  rcases D.pairList_mem_cases hS q hq with ⟨p,hp⟩ | ⟨b,hb⟩
  · exact couple_pairsAt_signs (D.couple p) S.sig _ _
      ((inflatedPosition_sign S D.tree _).trans (sourcePair_first_sign S hS p))
      ((inflatedPosition_sign S D.tree _).trans (sourcePair_second_sign S hS p)) q hp
  · exact chain_pairsAt_signs (D.tree b) S.sig (nodeSign S.sig b.1) _
      (inflatedPosition_sign S D.tree b.toNode) q hb

end WaveTurbulence.Reg.Skeleton
