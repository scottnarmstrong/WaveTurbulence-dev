/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CompletePairListNodup

/-! # No duplicate pair blocks occur in literal reconstruction data -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.pairList_nodup {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : (D.pairList hS).Nodup :=
  completePairList_nodup (D.forest hS) (D.pairList hS) (D.pairList_endpoints_valid hS)
    (D.forest_pairList_cover hS) (D.pairList_endpoint_count hS)

end WaveTurbulence.Reg.Skeleton
