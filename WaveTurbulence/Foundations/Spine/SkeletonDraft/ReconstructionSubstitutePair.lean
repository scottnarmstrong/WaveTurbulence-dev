/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.PositionCongruenceLonePath

/-! # Global exact pair substitution in regular reconstruction assignments -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Substitute in all literal code blocks; blocks missing the target pair stay unchanged. -/
noncomputable def ReconstructionData.substitutePair {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (x y : Address w) (Q : RegCpl) : ReconstructionData S where
  tree := fun b => normalizeChain (substituteChainPair (D.tree b) (nodeSign S.sig b.1)
    (inflatedPosition S D.tree b.toNode) x y Q)
  couple := fun p => normalizeCouple (substituteCouplePair (D.couple p)
    (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
    (inflatedPosition S D.tree (p.secondLeaf hS).toNode) x y Q)
  tree_wf := fun _ => normalizeChain_wf _
  couple_wf := fun _ => normalizeCouple_wf _

theorem ReconstructionData.substitutePair_position {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (x y : Address w) (Q : RegCpl) (a : GNode S.tree) :
    inflatedPosition S (D.substitutePair hS x y Q).tree a = inflatedPosition S D.tree a := by
  apply inflatedPosition_congr_lonePath
  intro b
  exact (normalizeChain_lonePath _).trans (substituteChainPair_lonePath _ _ _ _ _ _)

end WaveTurbulence.Reg.Skeleton
