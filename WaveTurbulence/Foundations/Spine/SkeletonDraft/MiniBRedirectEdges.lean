/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBPortRange
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CollapseIncomingRedirect
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.DipoleSpliceFormula

/-! # Exact free-splice transport of surviving B-mini graph edges -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem miniB_contract_redirect {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniTreeCode} (h : MiniBOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) (r : (Fin w ⊕ B) × Fin 4)
    (hra : r ≠ (.inr (G.label b),0)) (hrx : r ≠ G.incoming b.toNode)
    (hr : redirect (G.incoming (c.child k.lone)) (G.incoming b.toNode) r ∈
      Set.range (G.collapsePairedTree (h.isSubPairedTree hG)).portEmbedding) :
    (G.graphDipole_of_branch hG h.branchDipole).contract
        (redirect (G.incoming (c.child k.lone)) (G.incoming b.toNode) r) =
      redirect (G.incoming (c.child k.lone)) (G.incoming b.toNode) (G.graph.mate r) := by
  let D := G.graphDipole_of_branch hG h.branchDipole
  let z := redirect (G.incoming (c.child k.lone)) (G.incoming b.toNode) r
  have hz := (G.miniB_port_range h hG z).mp hr
  have hxne : G.incoming b.toNode ≠ G.incoming (c.child k.lone) := by
    intro he
    have he' := congrArg (fun a : GNode G.garden.tree => a.1.2.length) (G.incoming_injective he)
    rw [h.lone_frame] at he'
    change b.1.2.length = (b.1.2 ++ [k.c,k.lone]).length at he'
    simp only [List.length_append,List.length_cons,List.length_nil] at he'
    omega
  have hfree : (D.v,D.perm D.free) = G.incoming (c.child k.lone) :=
    (G.incoming_child c k.lone).symm
  have hmb : G.graph.mate (G.incoming (c.child k.lone)) ≠ G.incoming (c.child k.lone) := by
    rw [G.incoming_child]
    exact G.graph_branch_active hG c k.lone.succ
  calc
    D.contract z = splice G.graph.mate (.inr (G.label b),0) (D.v,D.perm D.free) z :=
      D.contract_outside_free G.graph.involutive z hz.2.1 hz.2.2
    _ = splice G.graph.mate (.inr (G.label b),0) (G.incoming (c.child k.lone)) z := by rw [hfree]
    _ = redirect (G.incoming (c.child k.lone)) (G.incoming b.toNode) (G.graph.mate r) :=
      splice_redirect G.graph.mate G.graph.involutive _ _ _ r
        (G.incoming_ne_parent b.toNode (G.label b)) hxne (G.graph_mate_incoming_branch b) hmb hra hrx

end WaveTurbulence.Reg.Skeleton.LabelledGarden
