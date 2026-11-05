/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.LabelledGraph

/-! # Incoming source slots distinguish branching nodes from leaves -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem portMate_encode {w : ℕ} (G : Garden w) (x : Incidence G) :
    portMate G (encodeIncidence G x) = encodeIncidence G (incidenceMate G x) := by
  change portEquiv G (incidenceMate G ((portEquiv G).symm (portEquiv G x))) =
    portEquiv G (incidenceMate G x)
  rw [Equiv.symm_apply_apply]

theorem portMate_parent {w : ℕ} (G : Garden w) (b : GBranch G.tree) :
    portMate G (.inr (b,0)) = encodeIncidence G (.inl b.toNode) := by
  change portMate G (encodeIncidence G (.inr b)) = _
  rw [portMate_encode,incidenceMate_parent]

namespace LabelledGarden

/-- The original root/child slot that points into an actual source node. -/
def incoming {w : ℕ} {B : Type*} (G : LabelledGarden w B) (a : GNode G.garden.tree) :
    (Fin w ⊕ B) × Fin 4 := G.portEmbedding (encodeIncidence G.garden (.inl a))

/-- Incoming node slots are distinct, including all root and child positions. -/
theorem incoming_injective {w : ℕ} {B : Type*} (G : LabelledGarden w B) : Function.Injective G.incoming := by
  intro a b h
  exact Sum.inl.inj ((portEquiv G.garden).injective (G.portEmbedding.injective h))

/-- A root's incoming slot is precisely its fixed root port. -/
theorem incoming_root {w : ℕ} {B : Type*} (G : LabelledGarden w B) (j : Fin w) :
    G.incoming (GNode.root G.garden.tree j) = (.inl j,0) := rfl

/-- Child slots retain their ordered position and original parent label. -/
theorem incoming_child {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (b : GBranch G.garden.tree) (i : Fin 3) : G.incoming (b.child i) = (.inr (G.label b),i.succ) := by
  rw [incoming,encodeIncidence_child]
  rfl

/-- No incoming node slot is a branch parent port. -/
theorem incoming_ne_parent {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (a : GNode G.garden.tree) (b : B) : G.incoming a ≠ (.inr b,0) := by
  intro he
  unfold incoming encodeIncidence at he
  cases hs : nodeToSlot a with
  | inl j =>
    simp only [hs] at he
    have hv : (Sum.inl j : Fin w ⊕ B) = .inr b := congrArg Prod.fst he
    cases hv
  | inr p =>
    obtain ⟨c,i⟩ := p
    simp only [hs] at he
    have hi : i.succ = (0 : Fin 4) := congrArg Prod.snd he
    exact Fin.succ_ne_zero i hi

/-- The mate of an incoming branching node is its own parent port. -/
theorem graph_mate_incoming_branch {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (b : GBranch G.garden.tree) : G.graph.mate (G.incoming b.toNode) = (.inr (G.label b),0) := by
  rw [incoming,graph_mate_embedding,portMate_encode,incidenceMate_branch]
  rfl

/-- The mate of an incoming leaf is the incoming slot of its actual partner leaf. -/
theorem graph_mate_incoming_leaf {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (ℓ : GLeaf G.garden.tree) : G.graph.mate (G.incoming ℓ.toNode) = G.incoming (G.garden.pair ℓ).toNode := by
  rw [incoming,graph_mate_embedding,portMate_encode,incidenceMate_leaf]
  rfl

/-- The graph also retains the incoming neighbour of every branch parent port. -/
theorem graph_mate_parent {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (b : GBranch G.garden.tree) : G.graph.mate (.inr (G.label b),0) = G.incoming b.toNode := by
  change G.graph.mate (G.portEmbedding (.inr (b,0))) = _
  rw [graph_mate_embedding,portMate_parent]
  rfl

/-- Detect the exact source branch and its label from the mate of its incoming slot. -/
theorem branch_of_mate_incoming {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (a : GNode G.garden.tree) (b : B) (he : G.graph.mate (G.incoming a) = (.inr b,0)) :
    ∃ c : GBranch G.garden.tree, c.toNode = a ∧ G.label c = b := by
  rcases (Comb.TreePath.mem_nodes_iff _ _).mp a.2 with hl | hb
  · let ℓ : GLeaf G.garden.tree := ⟨a.1,hl⟩
    have ha : a = ℓ.toNode := Subtype.ext rfl
    rw [ha,graph_mate_incoming_leaf] at he
    exact (G.incoming_ne_parent _ b he).elim
  · let c : GBranch G.garden.tree := ⟨a.1,hb⟩
    have ha : a = c.toNode := Subtype.ext rfl
    rw [ha,graph_mate_incoming_branch] at he
    exact ⟨c,ha.symm,Sum.inr.inj (congrArg Prod.fst he)⟩

end LabelledGarden
end WaveTurbulence.Reg.Skeleton
