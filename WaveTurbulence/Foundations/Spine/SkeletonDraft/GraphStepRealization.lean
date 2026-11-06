/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReductionTraceGraph

/-! # Every labelled matching contraction of an ordinary garden is an actual source surgery -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem LabelledGarden.realize_graph_step {w : ℕ} {B : Type*} [DecidableEq B]
    (G : LabelledGarden w B) (hG : G.garden.IsPlain) (N : PortMatching (Fin w ⊕ B))
    (h : PortMatching.Step G.graph N) :
    ∃ H : Garden w, H.IsPlain ∧ ∃ T : ReductionTrace G.garden H,
      (LabelledGarden.mk H (T.branches.trans G.label)).graph = N := by
  obtain ⟨D,hD⟩ := h
  obtain ⟨E,hu,hv,hperm,hfree⟩ := G.branchDipole_of_graph hG D
  obtain ⟨o,ho⟩ := E.exists_sourceMini hG
  cases o with
  | opA b c k hm =>
    let F := G.graphDipole_of_branch hG (hm.branchDipole hG)
    have hvertices : (F.u = D.u ∧ F.v = D.v) ∨ (F.u = D.v ∧ F.v = D.u) := by
      rcases ho with ⟨hb,hc⟩ | ⟨hb,hc⟩
      · exact Or.inl ⟨(congrArg (fun b => Sum.inr (G.label b)) hb).trans hu.symm,
          (congrArg (fun b => Sum.inr (G.label b)) hc).trans hv.symm⟩
      · exact Or.inr ⟨(congrArg (fun b => Sum.inr (G.label b)) hb).trans hv.symm,
          (congrArg (fun b => Sum.inr (G.label b)) hc).trans hu.symm⟩
    refine ⟨collapseCoupleGarden (hm.isSubCouple hG),collapseCoupleGarden_plain _ hG,
      ReductionTrace.opA G.garden hG b c k hm,?_⟩
    apply PortMatching.ext
    exact (G.miniA_graph_contract hm hG).trans
      ((F.contract_eq_of_unordered D G.graph.involutive hvertices).trans hD.symm)
  | opB b c k hm =>
    let F := G.graphDipole_of_branch hG hm.branchDipole
    have hvertices : (F.u = D.u ∧ F.v = D.v) ∨ (F.u = D.v ∧ F.v = D.u) := by
      rcases ho with ⟨hb,hc⟩ | ⟨hb,hc⟩
      · exact Or.inl ⟨(congrArg (fun b => Sum.inr (G.label b)) hb).trans hu.symm,
          (congrArg (fun b => Sum.inr (G.label b)) hc).trans hv.symm⟩
      · exact Or.inr ⟨(congrArg (fun b => Sum.inr (G.label b)) hb).trans hv.symm,
          (congrArg (fun b => Sum.inr (G.label b)) hc).trans hu.symm⟩
    refine ⟨collapsePairedTreeGarden (hm.isSubPairedTree hG),collapsePairedTreeGarden_plain _ hG,
      ReductionTrace.opB G.garden hG b c k hm,?_⟩
    apply PortMatching.ext
    exact (G.miniB_graph_contract hm hG).trans
      ((F.contract_eq_of_unordered D G.graph.involutive hvertices).trans hD.symm)

end WaveTurbulence.Reg.Skeleton
