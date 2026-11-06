/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CollapseIncomingPayload
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.IncomingPorts

/-! # Exact surviving edges and boundary reconnection for arbitrary source couple collapse -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem collapseCouple_graph_parent_unchanged {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b)
    (d : GBranch (collapseCoupleGarden h).tree) :
    (G.collapseCouple h).graph.mate (.inr ((G.collapseCouple h).label d),0) =
      G.graph.mate (.inr (G.label (collapseCoupleBranchEmbedding h d)),0) := by
  exact ((G.collapseCouple h).graph_mate_parent d).trans
    ((G.collapseCouple_incoming h d.toNode).trans
      (G.graph_mate_parent (collapseCoupleBranchEmbedding h d)).symm)

theorem collapseCouple_graph_branch_incoming_unchanged {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b)
    (d : GBranch (collapseCoupleGarden h).tree) :
    (G.collapseCouple h).graph.mate ((G.collapseCouple h).incoming d.toNode) =
      G.graph.mate (G.incoming (collapseCoupleBranchEmbedding h d).toNode) := by
  exact ((G.collapseCouple h).graph_mate_incoming_branch d).trans
    (G.graph_mate_incoming_branch (collapseCoupleBranchEmbedding h d)).symm

theorem collapseCouple_graph_old_leaf_unchanged {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b)
    (ℓ : OutsideRoots G.garden.tree a b) :
    (G.collapseCouple h).graph.mate (G.incoming ℓ.1.toNode) = G.graph.mate (G.incoming ℓ.1.toNode) := by
  let L := G.collapseCouple h
  let e := collapseLeafEquiv G.garden.tree a b (Comb.subCouple_incomparable h)
  have hp := congrArg (fun z : GLeaf L.garden.tree => L.incoming z.toNode) (collapseCoupleGarden_pair_old h ℓ)
  exact (congrArg L.graph.mate (G.collapseCouple_incoming_old h ℓ).symm).trans
    ((L.graph_mate_incoming_leaf (e (.inl ℓ))).trans
      (hp.trans ((G.collapseCouple_incoming_old h _).trans (G.graph_mate_incoming_leaf ℓ.1).symm)))

theorem collapseCouple_graph_left_attachment {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b) :
    (G.collapseCouple h).graph.mate (G.incoming a) = G.incoming b := by
  let L := G.collapseCouple h
  let e := collapseLeafEquiv G.garden.tree a b (Comb.subCouple_incomparable h)
  have hp := congrArg (fun z : GLeaf L.garden.tree => L.incoming z.toNode) (collapseCoupleGarden_pair_left h)
  exact (congrArg L.graph.mate (G.collapseCouple_incoming_left h).symm).trans
    ((L.graph_mate_incoming_leaf (e (.inr 0))).trans (hp.trans (G.collapseCouple_incoming_right h)))

theorem collapseCouple_graph_right_attachment {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b) :
    (G.collapseCouple h).graph.mate (G.incoming b) = G.incoming a := by
  let L := G.collapseCouple h
  let e := collapseLeafEquiv G.garden.tree a b (Comb.subCouple_incomparable h)
  have hp := congrArg (fun z : GLeaf L.garden.tree => L.incoming z.toNode) (collapseCoupleGarden_pair_right h)
  exact (congrArg L.graph.mate (G.collapseCouple_incoming_right h).symm).trans
    ((L.graph_mate_incoming_leaf (e (.inr 1))).trans (hp.trans (G.collapseCouple_incoming_left h)))

end WaveTurbulence.Reg.Skeleton.LabelledGarden
