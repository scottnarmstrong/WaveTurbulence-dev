/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleCollapseGraphEdges
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubforestOpenBoundary

/-! # Surviving ambient active edges outside an entire collapsed subcouple are unchanged -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem collapseCouple_leaf_edge_outside {w : ℕ} (G : Garden w) {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) (ℓ : GLeaf (collapseCoupleGarden h).tree)
    (hx : ((ambientWithPadding (v := 2) G).collapseCouple h).incoming ℓ.toNode ∉
      Set.range (subforestOpenGraph G (Comb.twoRootSubforest a b (Comb.subCouple_incomparable h))
        (Comb.subCouple_forest_closed h)).port) :
    ((ambientWithPadding (v := 2) G).collapseCouple h).graph.mate
      (((ambientWithPadding (v := 2) G).collapseCouple h).incoming ℓ.toNode) =
    (ambientWithPadding (v := 2) G).graph.mate
      (((ambientWithPadding (v := 2) G).collapseCouple h).incoming ℓ.toNode) := by
  let A := ambientWithPadding (v := 2) G
  let L := A.collapseCouple h
  let E := Comb.twoRootSubforest a b (Comb.subCouple_incomparable h)
  let O := subforestOpenGraph G E (Comb.subCouple_forest_closed h)
  let C := collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h)
  obtain ⟨y,hy⟩ := C.surjective ℓ
  cases y with
  | inl z =>
    have hi : L.incoming ℓ.toNode = A.incoming z.1.toNode :=
      (congrArg (fun ℓ : GLeaf L.garden.tree => L.incoming ℓ.toNode) hy.symm).trans
        (A.collapseCouple_incoming_old h z)
    exact (congrArg L.graph.mate hi).trans ((A.collapseCouple_graph_old_leaf_unchanged h z).trans
      (congrArg A.graph.mate hi.symm))
  | inr i =>
    have hroot : O.port (.inl i,0) = A.incoming (E.root i) := subforestOpenPort_root_zero G E _ i
    have hi : L.incoming ℓ.toNode = A.incoming (E.root i) := by
      fin_cases i
      · exact (congrArg (fun ℓ : GLeaf L.garden.tree => L.incoming ℓ.toNode) hy.symm).trans
          (A.collapseCouple_incoming_left h)
      · exact (congrArg (fun ℓ : GLeaf L.garden.tree => L.incoming ℓ.toNode) hy.symm).trans
          (A.collapseCouple_incoming_right h)
    exact (hx ⟨(.inl i,0),hroot.trans hi.symm⟩).elim

theorem collapseCouple_active_edge_outside {w : ℕ} (G : Garden w) {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) (x : (Fin w ⊕ (GBranch G.tree ⊕ Fin 2)) × Fin 4)
    (hx : x ∉ Set.range (subforestOpenGraph G (Comb.twoRootSubforest a b (Comb.subCouple_incomparable h))
      (Comb.subCouple_forest_closed h)).port)
    (ha : x ∈ Set.range ((ambientWithPadding (v := 2) G).collapseCouple h).portEmbedding) :
    ((ambientWithPadding (v := 2) G).collapseCouple h).graph.mate x =
      (ambientWithPadding (v := 2) G).graph.mate x := by
  let A := ambientWithPadding (v := 2) G
  let L := A.collapseCouple h
  obtain ⟨p,rfl⟩ := ha
  obtain ⟨z,rfl⟩ := (portEquiv L.garden).surjective p
  cases z with
  | inr d => exact A.collapseCouple_graph_parent_unchanged h d
  | inl n =>
    rcases (Comb.TreePath.mem_nodes_iff _ _).mp n.2 with hl | hb
    · let ℓ : GLeaf L.garden.tree := ⟨n.1,hl⟩
      have he : ℓ.toNode = n := Subtype.ext rfl
      have hx' : L.incoming ℓ.toNode ∉ Set.range (subforestOpenGraph G
          (Comb.twoRootSubforest a b (Comb.subCouple_incomparable h)) (Comb.subCouple_forest_closed h)).port :=
        he.symm ▸ hx
      exact he ▸ collapseCouple_leaf_edge_outside G h ℓ hx'
    · let d : GBranch L.garden.tree := ⟨n.1,hb⟩
      have he : d.toNode = n := Subtype.ext rfl
      have hi := A.collapseCouple_incoming h d.toNode
      have hh := (A.collapseCouple_graph_branch_incoming_unchanged h d).trans
        (congrArg A.graph.mate hi.symm)
      exact he ▸ hh

end WaveTurbulence.Reg.Skeleton
