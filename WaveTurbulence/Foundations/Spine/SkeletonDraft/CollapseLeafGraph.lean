/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CollapseIncomingPayload

/-! # Literal graph edges of the actual collapsed-couple leaf payload -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem collapseCouple_graph_leaf_payload {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b)
    (z : OutsideRoots G.garden.tree a b ⊕ Fin 2) :
    let E := collapseLeafEquiv G.garden.tree a b (Comb.subCouple_incomparable h)
    (G.collapseCouple h).graph.mate ((G.collapseCouple h).incoming (E z).toNode) =
      (G.collapseCouple h).incoming (E ((collapsedPairing h).pair z)).toNode := by
  dsimp only
  exact ((G.collapseCouple h).graph_mate_incoming_leaf _).trans
    (congrArg (fun q : GLeaf (collapseCoupleGarden h).tree => (G.collapseCouple h).incoming q.toNode)
      (collapseCoupleGarden_pair_payload h z))

theorem collapseCouple_graph_leaf_old {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b)
    (ℓ : OutsideRoots G.garden.tree a b) :
    let E := collapseLeafEquiv G.garden.tree a b (Comb.subCouple_incomparable h)
    (G.collapseCouple h).graph.mate ((G.collapseCouple h).incoming (E (.inl ℓ)).toNode) =
      G.incoming (G.garden.pair ℓ.1).toNode := by
  exact (G.collapseCouple_graph_leaf_payload h (.inl ℓ)).trans (G.collapseCouple_incoming_old h _)

theorem collapseCouple_graph_leaf_left {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b) :
    let E := collapseLeafEquiv G.garden.tree a b (Comb.subCouple_incomparable h)
    (G.collapseCouple h).graph.mate ((G.collapseCouple h).incoming (E (.inr 0)).toNode) =
      G.incoming b := by
  exact (G.collapseCouple_graph_leaf_payload h (.inr 0)).trans (G.collapseCouple_incoming_right h)

theorem collapseCouple_graph_leaf_right {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b) :
    let E := collapseLeafEquiv G.garden.tree a b (Comb.subCouple_incomparable h)
    (G.collapseCouple h).graph.mate ((G.collapseCouple h).incoming (E (.inr 1)).toNode) =
      G.incoming a := by
  exact (G.collapseCouple_graph_leaf_payload h (.inr 1)).trans (G.collapseCouple_incoming_left h)

end WaveTurbulence.Reg.Skeleton.LabelledGarden
