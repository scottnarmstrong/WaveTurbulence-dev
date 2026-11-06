/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleCollapseOutsideRange

/-! # Complete ambient matching locality of arbitrary ordinary couple collapse -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem collapseCouple_matching_outside {w : ℕ} (G : Garden w)
    {a b : GNode G.tree} (h : Comb.IsSubCouple G a b)
    (x : (Fin w ⊕ (GBranch G.tree ⊕ Fin 2)) × Fin 4)
    (hx : x ∉ Set.range (subforestOpenGraph G (Comb.twoRootSubforest a b (Comb.subCouple_incomparable h))
      (Comb.subCouple_forest_closed h)).port) :
    ((ambientWithPadding (v := 2) G).collapseCouple h).graph.mate x =
      (ambientWithPadding (v := 2) G).graph.mate x := by
  let A := ambientWithPadding (v := 2) G
  let L := A.collapseCouple h
  by_cases ha : x ∈ Set.range L.portEmbedding
  · exact collapseCouple_active_edge_outside G h x hx ha
  · have hn : x ∉ Set.range A.portEmbedding := fun hm => ha (collapseCouple_port_survives_outside G h x hx hm)
    exact (extendMate_outside _ _ x ha).trans (extendMate_outside _ _ x hn).symm

end WaveTurbulence.Reg.Skeleton
