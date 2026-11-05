/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionInsertMiniPositions
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionCoupleLocation
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CoupleInsertionPairTransport
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainInsertionPairTransport

/-! # Exact local matching update for every reconstruction block -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

noncomputable def ReconstructionData.nodeBlock {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : ReplacementSlot S → Finset (Address w)
  | .inl p => coupleNodes (D.couple p) (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode)
  | .inr b => chainNodes (D.tree b) (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode) ∪
      {D.corePosition b}

theorem ReconstructionData.insertMini_pairBlock {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (target : GNode (D.forest hS))
    (m : MiniTreeCode) (slot : ReplacementSlot S) :
    (D.insertMini hS target.1 m).pairBlock hS slot =
      (D.pairBlock hS slot).image (fun p =>
        (relocate target.1 m.c m.lone p.1,relocate target.1 m.c m.lone p.2)) ∪
      if target.1 ∈ D.nodeBlock hS slot then miniPairs S.sig target.1 m else ∅ := by
  classical
  cases slot with
  | inl p =>
    change (((D.insertMini hS target.1 m).couple p).pairsAt _ _).toFinset = _
    rw [D.insertMini_position hS target m,D.insertMini_position hS target m]
    exact normalizedCouple_pairs_pinned (D.couple p) S.sig _ _ target.1 m
      (D.couple_frame_incomp hS p)
      ((inflatedPosition_sign S D.tree _).trans (sourcePair_first_sign S hS p))
      ((inflatedPosition_sign S D.tree _).trans (sourcePair_second_sign S hS p))
      (D.node_couple_location hS target p)
  | inr b =>
    change (((D.insertMini hS target.1 m).tree b).pairsAt _ _).toFinset = _
    rw [D.insertMini_position hS target m]
    have he := normalizedChain_pairs_pinned (D.tree b) S.sig (nodeSign S.sig b.1)
      (inflatedPosition S D.tree b.toNode) target.1 m (inflatedPosition_sign S D.tree b.toNode)
      (D.node_chain_location hS target b)
    simp only [ReconstructionData.insertMini,ReconstructionData.corePosition,
      ReconstructionData.pairBlock,ReconstructionData.nodeBlock,
      Finset.mem_union,Finset.mem_singleton] at *
    exact he

end WaveTurbulence.Reg.Skeleton
