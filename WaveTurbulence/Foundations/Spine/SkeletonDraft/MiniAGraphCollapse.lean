/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniALeafEdges
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniAParentEdges

/-! # Actual A-mini collapse is exactly its labelled graph contraction -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem miniA_graph_contract {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniCplCode} (h : MiniAOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) :
    (G.collapseCouple (h.isSubCouple hG)).graph.mate =
      (G.graphDipole_of_branch hG (h.branchDipole hG)).contract := by
  let S := G.collapseCouple (h.isSubCouple hG)
  let D := G.graphDipole_of_branch hG (h.branchDipole hG)
  have hp (d : GBranch S.garden.tree) : D.contract (.inr (S.label d),0) = S.incoming d.toNode :=
    (G.miniA_contract_parent h hG d).trans (S.graph_mate_parent d)
  have hn (a : GNode S.garden.tree) : D.contract (S.incoming a) = S.graph.mate (S.incoming a) := by
    rcases (Comb.TreePath.mem_nodes_iff _ _).mp a.2 with hl | hb
    · let ℓ : GLeaf S.garden.tree := ⟨a.1,hl⟩
      have he : ℓ.toNode = a := Subtype.ext rfl
      exact he ▸ G.miniA_contract_leaf h hG ℓ
    · let d : GBranch S.garden.tree := ⟨a.1,hb⟩
      have he : d.toNode = a := Subtype.ext rfl
      have hh := D.contract_involutive G.graph.involutive (.inr (S.label d),0)
      rw [hp d] at hh
      exact he ▸ hh.trans (S.graph_mate_incoming_branch d).symm
  funext x
  by_cases hx : x ∈ Set.range S.portEmbedding
  · obtain ⟨p,rfl⟩ := hx
    obtain ⟨z,rfl⟩ := (portEquiv S.garden).surjective p
    cases z with
    | inl a => exact (hn a).symm
    | inr d => exact (G.miniA_contract_parent h hG d).symm
  · have hs : S.graph.mate x = x := extendMate_outside _ _ x hx
    exact hs.trans (G.miniA_contract_inactive h hG x hx).symm

/-- Every actual source A-mini collapse is one step of the strongly confluent labelled matching reduction. -/
theorem miniA_graph_step {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniCplCode} (h : MiniAOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) :
    PortMatching.Step G.graph (G.collapseCouple (h.isSubCouple hG)).graph :=
  ⟨G.graphDipole_of_branch hG (h.branchDipole hG),G.miniA_graph_contract h hG⟩

end WaveTurbulence.Reg.Skeleton.LabelledGarden
