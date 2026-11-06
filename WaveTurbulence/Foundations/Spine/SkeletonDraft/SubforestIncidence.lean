/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SubforestMinis

/-! # Exact matching embedding of an actual pairing-closed rooted subforest -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

def subforestIncidenceEmbedding {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) : Incidence (E.inducedGarden hc) ↪ Incidence G :=
  E.nodeEmbedding.sumMap (subforestBranchEmbedding E)

theorem subforestIncidence_mate {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (x : Incidence (E.inducedGarden hc)) :
    incidenceMate G (subforestIncidenceEmbedding G E hc x) =
      subforestIncidenceEmbedding G E hc (incidenceMate (E.inducedGarden hc) x) := by
  cases x with
  | inr b =>
    change incidenceMate G (.inr (subforestBranchEmbedding E b)) = .inl (E.nodeEmbedding b.toNode)
    rw [incidenceMate_parent]
    exact congrArg Sum.inl (subforest_branch_node E b).symm
  | inl a =>
    rcases (Comb.TreePath.mem_nodes_iff _ _).mp a.2 with hl | hb
    · let ℓ : GLeaf (E.inducedGarden hc).tree := ⟨a.1,hl⟩
      have ha : a = ℓ.toNode := Subtype.ext rfl
      rw [ha,incidenceMate_leaf]
      change incidenceMate G (.inl (E.nodeEmbedding ℓ.toNode)) =
        .inl (E.nodeEmbedding ((E.inducedGarden hc).pair ℓ).toNode)
      have hp : (G.pair (E.leafEmbedding ℓ)).toNode =
          E.nodeEmbedding ((E.inducedGarden hc).pair ℓ).toNode :=
        (congrArg (fun q : GLeaf G.tree => q.toNode) (E.inducedGarden_pair hc ℓ)).symm.trans
          (subforest_leaf_node E _)
      exact (congrArg (fun y : GNode G.tree => incidenceMate G (.inl y)) (subforest_leaf_node E ℓ).symm).trans
        ((incidenceMate_leaf G (E.leafEmbedding ℓ)).trans (congrArg Sum.inl hp))
    · let b : GBranch (E.inducedGarden hc).tree := ⟨a.1,hb⟩
      have ha : a = b.toNode := Subtype.ext rfl
      rw [ha,incidenceMate_branch]
      change incidenceMate G (.inl (E.nodeEmbedding b.toNode)) = .inr (subforestBranchEmbedding E b)
      exact (congrArg (fun y : GNode G.tree => incidenceMate G (.inl y)) (subforest_branch_node E b)).trans
        (incidenceMate_branch G (subforestBranchEmbedding E b))

/-- Exact actual-port embedding, including the source root attachment ports. -/
noncomputable def subforestPortEmbedding {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) : Port (E.inducedGarden hc) ↪ Port G :=
  (portEquiv (E.inducedGarden hc)).symm.toEmbedding |>.trans
    ((subforestIncidenceEmbedding G E hc).trans (portEquiv G).toEmbedding)

theorem subforestPort_mate {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (p : Port (E.inducedGarden hc)) :
    portMate G (subforestPortEmbedding G E hc p) =
      subforestPortEmbedding G E hc (portMate (E.inducedGarden hc) p) := by
  change portMate G (encodeIncidence G ((subforestIncidenceEmbedding G E hc)
    ((portEquiv (E.inducedGarden hc)).symm p))) = _
  rw [portMate_encode]
  change (portEquiv G) (incidenceMate G ((subforestIncidenceEmbedding G E hc) ((portEquiv (E.inducedGarden hc)).symm p))) =
    (portEquiv G) ((subforestIncidenceEmbedding G E hc)
      ((portEquiv (E.inducedGarden hc)).symm ((portEquiv (E.inducedGarden hc))
        (incidenceMate (E.inducedGarden hc) ((portEquiv (E.inducedGarden hc)).symm p)))))
  rw [Equiv.symm_apply_apply,subforestIncidence_mate]

end WaveTurbulence.Reg.Skeleton
