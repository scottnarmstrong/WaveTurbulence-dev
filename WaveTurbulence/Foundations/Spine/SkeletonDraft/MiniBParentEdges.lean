/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBRedirectEdges
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CollapseIncomingPayload

/-! # Exact B contraction at surviving branch parents and inactive labels -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem miniB_contract_parent {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniTreeCode} (h : MiniBOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) (d : GBranch (collapsePairedTreeGarden (h.isSubPairedTree hG)).tree) :
    let S := G.collapsePairedTree (h.isSubPairedTree hG)
    (G.graphDipole_of_branch hG h.branchDipole).contract (.inr (S.label d),0) =
      S.graph.mate (.inr (S.label d),0) := by
  let hs := h.isSubPairedTree hG
  let S := G.collapsePairedTree hs
  let e := collapsePairedTreeBranchEmbedding hs d
  let p : (Fin w ⊕ B) × Fin 4 := (.inr (S.label d),0)
  have hp : p ∈ Set.range S.portEmbedding := ⟨.inr (d,0),rfl⟩
  have hpa : p ≠ (.inr (G.label b),0) := fun he =>
    ((G.miniB_port_range h hG p).mp hp).2.1 (congrArg (fun z : (Fin w ⊕ B) × Fin 4 => z.1) he)
  have hpx : p ≠ G.incoming b.toNode := (G.incoming_ne_parent b.toNode (S.label d)).symm
  have hpr : redirect (G.incoming (c.child k.lone)) (G.incoming b.toNode) p = p :=
    ite_eq_right (G.incoming_ne_parent (c.child k.lone) (S.label d)).symm
  have hr : redirect (G.incoming (c.child k.lone)) (G.incoming b.toNode) p ∈ Set.range S.portEmbedding :=
    hpr.symm ▸ hp
  have hc := G.miniB_contract_redirect h hG p hpa hpx hr
  rw [hpr] at hc
  have hm : G.graph.mate p = G.incoming e.toNode := G.graph_mate_parent e
  have hi : S.incoming d.toNode =
      redirect (G.incoming (c.child k.lone)) (G.incoming b.toNode) (G.incoming e.toNode) :=
    G.collapsePairedTree_incoming_redirect hs d.toNode
  exact hc.trans ((congrArg (redirect (G.incoming (c.child k.lone)) (G.incoming b.toNode)) hm).trans
    (hi.symm.trans (S.graph_mate_parent d).symm))

theorem miniB_contract_inactive {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniTreeCode} (h : MiniBOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) (x : (Fin w ⊕ B) × Fin 4)
    (hx : x ∉ Set.range (G.collapsePairedTree (h.isSubPairedTree hG)).portEmbedding) :
    (G.graphDipole_of_branch hG h.branchDipole).contract x = x := by
  by_cases hb : x.1 = .inr (G.label b)
  · exact (G.graphDipole_of_branch hG h.branchDipole).contract_fixed x (Or.inl hb)
  by_cases hc : x.1 = .inr (G.label c)
  · exact (G.graphDipole_of_branch hG h.branchDipole).contract_fixed x (Or.inr hc)
  have ho : x ∉ Set.range G.portEmbedding := fun ho => hx ((G.miniB_port_range h hG x).mpr ⟨ho,hb,hc⟩)
  have hm : G.graph.mate x = x := extendMate_outside _ _ x ho
  exact foldSplice_fixed _ _ x hm

end WaveTurbulence.Reg.Skeleton.LabelledGarden
