/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedPairedTree

/-! # Exact non-lone partner transport in the actual source embedded paired tree -/

public section
namespace WaveTurbulence.Reg.Skeleton

 theorem embeddedPairedTree_pair_transport {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) (x : (Comb.collapseDataOfDesc h.1).OtherLeaf) :
    ∃ y : (Comb.collapseDataOfDesc h.1).OtherLeaf,
      (Comb.embeddedPairedTree h).pair x.1 = y.1 ∧
      Comb.CollapseData.leafEmbedding _ y = G.pair (Comb.CollapseData.leafEmbedding _ x) := by
  let D := Comb.collapseDataOfDesc h.1
  let f := Comb.CollapseData.leafEmbedding D
  let hc := Comb.CollapseData.closed_partner D h
  refine ⟨Comb.partnerPullback f hc x,?_,Comb.partnerPullback_spec f hc x⟩
  change Comb.pairWithLone (Comb.collapsedLone D.lower_eq) (Comb.partnerPullback f hc) x.1 = _
  exact Comb.pairWithLone_other _ _ x

end WaveTurbulence.Reg.Skeleton
