/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsePairedTreeNodes
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SpliceRedirect

/-! # One explicit incoming-slot redirection describes the entire paired-tree collapse -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem stretch_self {w : ℕ} (a : Address w) (p : Path) : stretch a p a = addrExt a p := by
  simp [stretch,addrExt,List.prefix_refl]

theorem collapsePairedTreeNodeEmbedding_eq_lower_iff {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) (x : GNode (collapsePairedTreeGarden h).tree) :
    collapsePairedTreeNodeEmbedding h x = b ↔ x.1 = a.1 := by
  have hb : b.1 = stretch a.1 (Comb.collapseDataOfDesc h.1).path a.1 :=
    (collapseData_frame h.1).trans (stretch_self a.1 _).symm
  constructor
  · intro he
    have hv := congrArg (fun z : GNode G.tree => z.1) he
    change stretch a.1 (Comb.collapseDataOfDesc h.1).path x.1 = b.1 at hv
    rw [hb] at hv
    exact stretch_injective a.1 _ hv
  · intro he
    apply Subtype.ext
    change stretch a.1 (Comb.collapseDataOfDesc h.1).path x.1 = b.1
    rw [he,← hb]

theorem LabelledGarden.collapsePairedTree_incoming_redirect {w : ℕ} {B : Type*} [DecidableEq B]
    (G : LabelledGarden w B) {a b : GNode G.garden.tree} (h : Comb.IsSubPairedTree G.garden a b)
    (x : GNode (collapsePairedTreeGarden h).tree) :
    (G.collapsePairedTree h).incoming x =
      redirect (G.incoming b) (G.incoming a) (G.incoming (collapsePairedTreeNodeEmbedding h x)) := by
  by_cases hx : x.1 = a.1
  · have he := (collapsePairedTreeNodeEmbedding_eq_lower_iff h x).mpr hx
    rw [redirect,he,ite_eq_left rfl]
    exact G.collapsePairedTree_incoming_boundary h x hx
  · have he : G.incoming (collapsePairedTreeNodeEmbedding h x) ≠ G.incoming b := by
      intro he
      exact hx ((collapsePairedTreeNodeEmbedding_eq_lower_iff h x).mp (G.incoming_injective he))
    rw [redirect,ite_eq_right he]
    exact G.collapsePairedTree_incoming_nonboundary h x hx

end WaveTurbulence.Reg.Skeleton
