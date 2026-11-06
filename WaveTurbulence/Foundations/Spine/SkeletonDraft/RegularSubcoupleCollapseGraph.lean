/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleCollapseInsideMatching
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleCollapseOutsideMatching
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.OpenReplacementUniqueness

/-! # Every actual regular embedded couple contracts to its literal ambient collapse graph -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem regular_subcouple_collapse_graph {w : ℕ} (G : Garden w) {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) (hr : IsRegularCouple (Comb.subCoupleGarden h)) :
    PortMatching.Reduces (ambientWithPadding (v := 2) G).graph
      ((ambientWithPadding (v := 2) G).collapseCouple h).graph := by
  classical
  let E := Comb.twoRootSubforest a b (Comb.subCouple_incomparable h)
  let hc := Comb.subCouple_forest_closed h
  let Q := E.inducedGarden hc
  let A := ambientWithPadding (v := 2) G
  let L := A.collapseCouple h
  let O := subforestOpenGraph G E hc
  obtain ⟨labelK,hlocal⟩ := (regularCouple_reduces_trivial hr).lift (Function.Embedding.refl (GBranch E.shape))
  let K := LabelledGarden.mk (decodedCouple .triv) labelK
  obtain ⟨U,F,hU,hport,houtside⟩ := PortMatching.OpenEmbedding.lift_reduces_outside hlocal A.graph O
  have hp (p) : F.port p = O.port p := by rw [hport]; rfl
  have hsame : U = L.graph := PortMatching.eq_of_matching_on_image_and_outside O.port A.graph U L.graph
    (fun p => (congrArg U.mate (hp p).symm).trans
      ((F.mate p).trans ((hp (K.graph.mate p)).trans (collapseCouple_matching_inside G h labelK p).symm)))
    houtside (fun x hx => collapseCouple_matching_outside G h x hx)
  exact hsame ▸ hU

end WaveTurbulence.Reg.Skeleton
