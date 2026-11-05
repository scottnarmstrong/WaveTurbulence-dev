/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreBranches
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.InsertionCovariance

/-! # Simultaneous mini-tree insertion in all reconstruction code blocks -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Insert at represented context nodes, appending at an original core node. -/
noncomputable def ReconstructionData.insertMini {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (target : Address w)
    (m : MiniTreeCode) : ReconstructionData S where
  tree := fun b => normalizeChain (if target = D.corePosition b then
    appendChain (D.tree b) (miniChain m) else
    insertMiniChain (D.tree b) (nodeSign S.sig b.1)
      (inflatedPosition S D.tree b.toNode) target m)
  couple := fun p => normalizeCouple (insertMiniCouple (D.couple p)
    (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
    (inflatedPosition S D.tree (p.secondLeaf hS).toNode) target m)
  tree_wf := fun _ => normalizeChain_wf _
  couple_wf := fun _ => normalizeCouple_wf _

end WaveTurbulence.Reg.Skeleton
