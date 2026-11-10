/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RegularSubcoupleCollapseGraph
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GraphHistoryRealization

/-! # Actual source erasure of every regular embedded couple with exact surviving branches -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem regular_subcouple_collapse_trace {w : ℕ} (G : Garden w) (hG : G.IsPlain)
    {a b : GNode G.tree} (h : Comb.IsSubCouple G a b)
    (hr : IsRegularCouple (Comb.subCoupleGarden h)) :
    ∃ T : ReductionTrace G (collapseCoupleGarden h), T.branches = collapseCoupleBranchEmbedding h := by
  classical
  let A := ambientWithPadding (v := 2) G
  let L := A.collapseCouple h
  obtain ⟨H,hH,T,hT⟩ := A.realize_graph_history hG L.graph (regular_subcouple_collapse_graph G h hr)
  let K := LabelledGarden.mk H (T.branches.trans A.label)
  have he : H = collapseCoupleGarden h := K.garden_eq_of_graph_eq L hH
    (collapseCoupleGarden_plain h hG) T.reduces.sig_eq hT
  subst H
  refine ⟨T,?_⟩
  apply Function.Embedding.ext
  intro d
  have hl := K.label_eq_of_address L hT d d rfl
  exact Sum.inl.inj hl

end WaveTurbulence.Reg.Skeleton
