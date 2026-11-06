/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniAPortRange
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.DipoleSpliceFormula
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CollapseIncomingPayload

/-! # Surviving A-mini graph edges and the two reconnected attachment slots -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem miniA_contract_retained_edge {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniCplCode} (h : MiniAOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) (x y : (Fin w ⊕ B) × Fin 4)
    (hx : x ∈ Set.range (G.collapseCouple (h.isSubCouple hG)).portEmbedding)
    (hy : y ∈ Set.range (G.collapseCouple (h.isSubCouple hG)).portEmbedding)
    (hm : G.graph.mate x = y) :
    (G.graphDipole_of_branch hG (h.branchDipole hG)).contract x = y := by
  have hx' := (G.miniA_port_range h hG x).mp hx
  have hy' := (G.miniA_port_range h hG y).mp hy
  apply Eq.trans ((G.graphDipole_of_branch hG (h.branchDipole hG)).contract_unaffected x hx'.2.1 hx'.2.2 ?_ ?_) hm
  · rw [hm]
    exact hy'.2.1
  · rw [hm]
    exact hy'.2.2

theorem miniA_contract_left_attachment {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniCplCode} (h : MiniAOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) :
    (G.graphDipole_of_branch hG (h.branchDipole hG)).contract (G.incoming b.toNode) =
      G.incoming c.toNode := by
  have hx : G.incoming b.toNode ∈ Set.range (G.collapseCouple (h.isSubCouple hG)).portEmbedding := by
    rw [← G.collapseCouple_incoming_left (h.isSubCouple hG)]
    exact (G.collapseCouple _).incoming_mem_range _
  have hx' := (G.miniA_port_range h hG _).mp hx
  rw [(G.graphDipole_of_branch hG (h.branchDipole hG)).contract_outside_free G.graph.involutive _ hx'.2.1 hx'.2.2]
  change splice G.graph.mate (.inr (G.label b),0) (.inr (G.label c),0) (G.incoming b.toNode) = _
  rw [splice_outside _ _ _ _ (G.incoming_ne_parent b.toNode (G.label b))
    (G.incoming_ne_parent b.toNode (G.label c)),G.graph_mate_incoming_branch,
    ite_eq_left rfl,G.graph_mate_parent]

theorem miniA_contract_right_attachment {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniCplCode} (h : MiniAOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) :
    (G.graphDipole_of_branch hG (h.branchDipole hG)).contract (G.incoming c.toNode) =
      G.incoming b.toNode := by
  have hx : G.incoming c.toNode ∈ Set.range (G.collapseCouple (h.isSubCouple hG)).portEmbedding := by
    rw [← G.collapseCouple_incoming_right (h.isSubCouple hG)]
    exact (G.collapseCouple _).incoming_mem_range _
  have hx' := (G.miniA_port_range h hG _).mp hx
  rw [(G.graphDipole_of_branch hG (h.branchDipole hG)).contract_outside_free G.graph.involutive _ hx'.2.1 hx'.2.2]
  change splice G.graph.mate (.inr (G.label b),0) (.inr (G.label c),0) (G.incoming c.toNode) = _
  rw [splice_symm]
  rw [splice_outside _ _ _ _ (G.incoming_ne_parent c.toNode (G.label c))
    (G.incoming_ne_parent c.toNode (G.label b)),G.graph_mate_incoming_branch,
    ite_eq_left rfl,G.graph_mate_parent]

end WaveTurbulence.Reg.Skeleton.LabelledGarden
