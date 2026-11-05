/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CarrierRoundTrip
public import WaveTurbulence.Foundations.WaveB.Molecules

/-! # The exact half-edge involution of a garden

An incoming slot at every node, together with a parent slot at every branching
node, gives the root and four branching ports. Parent-child edges join the two
slots at a branching node; leaf-pair edges join incoming slots at paired leaves.
No edge or branch label is forgotten.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Incoming root/child slots plus the parent slots of branching nodes. -/
abbrev Incidence {w : ℕ} (G : Garden w) := GNode G.tree ⊕ GBranch G.tree

/-- The actual source edges: either a parent-child edge or a paired-leaf edge. -/
def incidenceMate {w : ℕ} (G : Garden w) : Incidence G → Incidence G
  | .inr b => .inl b.toNode
  | .inl a => if h : a.1.2 ∈ (G.tree a.1.1).leaves then
      .inl (G.pair ⟨a.1,h⟩).toNode
    else .inr ⟨a.1,((Comb.TreePath.mem_nodes_iff _ _).mp a.2).resolve_left h⟩

theorem incidenceMate_parent {w : ℕ} (G : Garden w) (b : GBranch G.tree) :
    incidenceMate G (.inr b) = .inl b.toNode := rfl

theorem incidenceMate_branch {w : ℕ} (G : Garden w) (b : GBranch G.tree) :
    incidenceMate G (.inl b.toNode) = .inr b := by
  have hn : b.1.2 ∉ (G.tree b.1.1).leaves := fun h =>
    Comb.TreePath.not_mem_branching_of_mem_leaves _ h b.2
  simp [incidenceMate,GBranch.toNode,hn]
  rfl

theorem incidenceMate_leaf {w : ℕ} (G : Garden w) (ℓ : GLeaf G.tree) :
    incidenceMate G (.inl ℓ.toNode) = .inl (G.pair ℓ).toNode := by
  simp [incidenceMate,GLeaf.toNode,ℓ.2]
  rfl

/-- The port matching is involutive on its entire actual carrier. -/
theorem incidenceMate_involutive {w : ℕ} (G : Garden w) : Function.Involutive (incidenceMate G) := by
  intro x
  cases x with
  | inr b => rw [incidenceMate_parent,incidenceMate_branch]
  | inl a =>
    by_cases ha : a.1.2 ∈ (G.tree a.1.1).leaves
    · let ℓ : GLeaf G.tree := ⟨a.1,ha⟩
      have he : a = ℓ.toNode := Subtype.ext rfl
      rw [he,incidenceMate_leaf,incidenceMate_leaf,G.pair_pair]
    · let b : GBranch G.tree := ⟨a.1,((Comb.TreePath.mem_nodes_iff _ _).mp a.2).resolve_left ha⟩
      have he : a = b.toNode := Subtype.ext rfl
      rw [he,incidenceMate_branch,incidenceMate_parent]

/-- Ordinary gardens have no fixed half-edge: all their edges really join two slots. -/
theorem incidenceMate_ne {w : ℕ} (G : Garden w) (hG : G.IsPlain) (x : Incidence G) :
    incidenceMate G x ≠ x := by
  cases x with
  | inr b => rw [incidenceMate_parent]; simp
  | inl a =>
    by_cases ha : a.1.2 ∈ (G.tree a.1.1).leaves
    · let ℓ : GLeaf G.tree := ⟨a.1,ha⟩
      have he : a = ℓ.toNode := Subtype.ext rfl
      rw [he,incidenceMate_leaf]
      intro h
      have hn := Sum.inl.inj h
      apply Comb.pair_ne_of_plain hG ℓ
      exact Subtype.ext (congrArg (fun q : GNode G.tree => q.1) hn)
    · let b : GBranch G.tree := ⟨a.1,((Comb.TreePath.mem_nodes_iff _ _).mp a.2).resolve_left ha⟩
      have he : a = b.toNode := Subtype.ext rfl
      rw [he,incidenceMate_branch]
      simp

end WaveTurbulence.Reg.Skeleton
