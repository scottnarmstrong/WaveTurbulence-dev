/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairList
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionOrder
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceSlotCounts

/-! # Exact endpoint count for all literal reconstruction pairs, at arbitrary width -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.pairList_endpoint_count {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) :
    (D.pairList hS).length * 2 = Fintype.card (GLeaf (D.forest hS)) := by
  rw [D.pairList_length,Comb.card_gleaf,D.forest_order]
  have hc := sourcePair_card_twice S hS
  omega

end WaveTurbulence.Reg.Skeleton
