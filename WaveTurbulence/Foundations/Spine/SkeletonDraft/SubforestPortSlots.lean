/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubforestIncidence

/-! # Ordered internal ports and actual external roots of a subforest matching embedding -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem subforestPort_parent {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (b : GBranch E.shape) :
    subforestPortEmbedding G E hc (.inr (b,0)) = .inr (subforestBranchEmbedding E b,0) := rfl

theorem subforestPort_child {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (b : GBranch E.shape) (i : Fin 3) :
    subforestPortEmbedding G E hc (.inr (b,i.succ)) = .inr (subforestBranchEmbedding E b,i.succ) := by
  have hi := encodeIncidence_child (E.inducedGarden hc) b i
  change (portEquiv (E.inducedGarden hc)) (.inl (b.child i)) = .inr (b,i.succ) at hi
  rw [← hi]
  change (portEquiv G) (subforestIncidenceEmbedding G E hc
    ((portEquiv (E.inducedGarden hc)).symm ((portEquiv (E.inducedGarden hc)) (.inl (b.child i))))) = _
  rw [Equiv.symm_apply_apply]
  change encodeIncidence G (.inl (E.nodeEmbedding (b.child i))) = _
  exact (congrArg (fun a : GNode G.tree => encodeIncidence G (.inl a)) (subforest_node_child E b i)).trans
    (encodeIncidence_child G (subforestBranchEmbedding E b) i)

theorem subforestPort_branch {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (b : GBranch E.shape) (i : Fin 4) :
    subforestPortEmbedding G E hc (.inr (b,i)) = .inr (subforestBranchEmbedding E b,i) := by
  by_cases hi : i = 0
  · subst i
    exact subforestPort_parent G E hc b
  · obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    exact subforestPort_child G E hc b j

theorem subforestPort_root {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (j : Fin v) :
    subforestPortEmbedding G E hc (.inl j) = encodeIncidence G (.inl (E.root j)) := by
  change encodeIncidence G (.inl (E.nodeEmbedding (GNode.root E.shape j))) = _
  exact congrArg (fun a : GNode G.tree => encodeIncidence G (.inl a)) (subforest_node_root E j)

end WaveTurbulence.Reg.Skeleton
