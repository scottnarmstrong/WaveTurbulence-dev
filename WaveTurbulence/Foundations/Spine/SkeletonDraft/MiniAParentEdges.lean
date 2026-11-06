/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniARetainedEdges

/-! # Exact contraction comparison on surviving branch parents and inactive ports -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem miniA_contract_parent {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniCplCode} (h : MiniAOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) (d : GBranch (collapseCoupleGarden (h.isSubCouple hG)).tree) :
    let S := G.collapseCouple (h.isSubCouple hG)
    (G.graphDipole_of_branch hG (h.branchDipole hG)).contract (.inr (S.label d),0) =
      S.graph.mate (.inr (S.label d),0) := by
  let hs := h.isSubCouple hG
  let S := G.collapseCouple hs
  let e := collapseCoupleBranchEmbedding hs d
  have he : S.incoming d.toNode = G.incoming e.toNode :=
    (G.collapseCouple_incoming hs d.toNode).trans (congrArg G.incoming (Subtype.ext rfl))
  have hx : (Sum.inr (S.label d),0) ∈ Set.range S.portEmbedding := ⟨.inr (d,0),rfl⟩
  have hy : G.incoming e.toNode ∈ Set.range S.portEmbedding := he ▸ S.incoming_mem_range _
  have hm : G.graph.mate (.inr (S.label d),0) = G.incoming e.toNode := G.graph_mate_parent e
  exact (G.miniA_contract_retained_edge h hG _ _ hx hy hm).trans
    (he.symm.trans (S.graph_mate_parent d).symm)

theorem miniA_contract_inactive {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniCplCode} (h : MiniAOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) (x : (Fin w ⊕ B) × Fin 4)
    (hx : x ∉ Set.range (G.collapseCouple (h.isSubCouple hG)).portEmbedding) :
    (G.graphDipole_of_branch hG (h.branchDipole hG)).contract x = x := by
  by_cases hb : x.1 = .inr (G.label b)
  · exact (G.graphDipole_of_branch hG (h.branchDipole hG)).contract_fixed x (Or.inl hb)
  by_cases hc : x.1 = .inr (G.label c)
  · exact (G.graphDipole_of_branch hG (h.branchDipole hG)).contract_fixed x (Or.inr hc)
  have ho : x ∉ Set.range G.portEmbedding := fun ho => hx ((G.miniA_port_range h hG x).mpr ⟨ho,hb,hc⟩)
  have hm : G.graph.mate x = x := extendMate_outside _ _ x ho
  exact foldSplice_fixed _ _ x hm

end WaveTurbulence.Reg.Skeleton.LabelledGarden
