/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniARetainedEdges
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CollapseLeafGraph

/-! # Exact graph-contraction comparison at every surviving A-collapse leaf -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem miniA_contract_leaf {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniCplCode} (h : MiniAOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) (ℓ : GLeaf (collapseCoupleGarden (h.isSubCouple hG)).tree) :
    let S := G.collapseCouple (h.isSubCouple hG)
    (G.graphDipole_of_branch hG (h.branchDipole hG)).contract (S.incoming ℓ.toNode) =
      S.graph.mate (S.incoming ℓ.toNode) := by
  let hs := h.isSubCouple hG
  let E := collapseLeafEquiv G.garden.tree b.toNode c.toNode (Comb.subCouple_incomparable hs)
  let S := G.collapseCouple hs
  let D := G.graphDipole_of_branch hG (h.branchDipole hG)
  change D.contract (S.incoming ℓ.toNode) = S.graph.mate (S.incoming ℓ.toNode)
  obtain ⟨z,rfl⟩ := E.surjective ℓ
  cases z with
  | inl z =>
    have hx := G.collapseCouple_incoming_old hs z
    have hy := G.collapseCouple_incoming_old hs
      ⟨G.garden.pair z.1,outsideRoots_closed G.garden _ _ hs z.1 z.2⟩
    have hrx : G.incoming z.1.toNode ∈ Set.range S.portEmbedding := by
      exact hx ▸ S.incoming_mem_range _
    have hry : G.incoming (G.garden.pair z.1).toNode ∈ Set.range S.portEmbedding := by
      exact hy ▸ S.incoming_mem_range _
    exact (congrArg D.contract hx).trans
      ((G.miniA_contract_retained_edge h hG _ _ hrx hry (G.graph_mate_incoming_leaf z.1)).trans
        (G.collapseCouple_graph_leaf_old hs z).symm)
  | inr i =>
    fin_cases i
    · exact (congrArg D.contract (G.collapseCouple_incoming_left hs)).trans
        ((G.miniA_contract_left_attachment h hG).trans (G.collapseCouple_graph_leaf_left hs).symm)
    · exact (congrArg D.contract (G.collapseCouple_incoming_right hs)).trans
        ((G.miniA_contract_right_attachment h hG).trans (G.collapseCouple_graph_leaf_right hs).symm)

end WaveTurbulence.Reg.Skeleton.LabelledGarden
