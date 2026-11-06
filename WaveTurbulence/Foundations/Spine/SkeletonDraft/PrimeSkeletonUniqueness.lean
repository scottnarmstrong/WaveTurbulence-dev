/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GardenGraphHistories
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.PrimeGraph

/-! # Native prime skeleton uniqueness for arbitrary ordinary couples and gardens

DH21 Proposition 4.13 and DH21-2 Proposition 4.4. The hypotheses are actual
source inverse-surgery histories, never abstract graph confluence premises.
-/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- Any two actual prime gardens obtained by source A/B reduction are literally equal,
including root order/signature, ordered trees and all actual leaf partners. -/
theorem prime_skeleton_unique {w : ℕ} (G H K : Garden w)
    (hH : IsPrimeGarden H) (hK : IsPrimeGarden K)
    (hGH : GardenReduces G H) (hGK : GardenReduces G K) : H = K := by
  classical
  let label : GBranch G.tree ↪ GBranch G.tree := Function.Embedding.refl _
  obtain ⟨labelH,hrH⟩ := hGH.lift label
  obtain ⟨labelK,hrK⟩ := hGK.lift label
  let LG : LabelledGarden w (GBranch G.tree) := ⟨G,label⟩
  let LH : LabelledGarden w (GBranch G.tree) := ⟨H,labelH⟩
  let LK : LabelledGarden w (GBranch G.tree) := ⟨K,labelK⟩
  exact LH.prime_eq_of_graph_reductions LK LG.graph hH hK
    (hGH.sig_eq.trans hGK.sig_eq.symm) hrH hrK

end WaveTurbulence.Reg.Skeleton
