/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.IncomingPorts

/-! # Exact source meanings of bonds between ordered branching ports -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- An incoming source slot can never be a branch parent slot. -/
theorem encode_incoming_ne_parent {w : ℕ} (G : Garden w) (a : GNode G.tree) (b : GBranch G.tree) :
    encodeIncidence G (.inl a) ≠ .inr (b,0) := by
  intro he
  have h : (portEquiv G) (.inl a) = (portEquiv G) (.inr b) := he
  have hi := (portEquiv G).injective h
  cases hi

/-- Parent-to-child bonds are exactly the original ordered tree edges. -/
theorem portMate_parent_child_iff {w : ℕ} (G : Garden w) (b c : GBranch G.tree) (i : Fin 3) :
    portMate G (.inr (b,0)) = .inr (c,i.succ) ↔ b.toNode = c.child i := by
  rw [portMate_parent,← encodeIncidence_child G c i]
  constructor
  · intro h
    have he : portEquiv G (.inl b.toNode) = portEquiv G (.inl (c.child i)) := h
    exact Sum.inl.inj ((portEquiv G).injective he)
  · intro h
    exact congrArg (fun a : GNode G.tree => encodeIncidence G (.inl a)) h

/-- The source forest never joins two branch parent ports. -/
theorem portMate_parent_ne_parent {w : ℕ} (G : Garden w) (b c : GBranch G.tree) :
    portMate G (.inr (b,0)) ≠ .inr (c,0) := by
  rw [portMate_parent]
  exact encode_incoming_ne_parent G b.toNode c

/-- Child-to-parent bonds are the same exact source tree edges, read backwards. -/
theorem portMate_child_parent_iff {w : ℕ} (G : Garden w) (b c : GBranch G.tree) (i : Fin 3) :
    portMate G (.inr (b,i.succ)) = .inr (c,0) ↔ b.child i = c.toNode := by
  constructor
  · intro he
    have hh := portMate_involutive G (.inr (b,i.succ))
    rw [he] at hh
    exact ((portMate_parent_child_iff G c b i).mp hh).symm
  · intro he
    have hh := (portMate_parent_child_iff G c b i).mpr he.symm
    have hi := portMate_involutive G (.inr (c,0))
    rw [hh] at hi
    exact hi

/-- A cycle of two parent-child edges contradicts actual path lengths. -/
theorem not_mutual_children {w : ℕ} (G : Garden w) (b c : GBranch G.tree) (i j : Fin 3) :
    ¬ (b.toNode = c.child i ∧ c.toNode = b.child j) := by
  rintro ⟨hb,hc⟩
  have h0 := congrArg (fun a : GNode G.tree => a.1.2.length) hb
  have h1 := congrArg (fun a : GNode G.tree => a.1.2.length) hc
  change b.1.2.length = (c.1.2 ++ [i]).length at h0
  change c.1.2.length = (b.1.2 ++ [j]).length at h1
  simp only [List.length_append,List.length_singleton] at h0 h1
  omega

/-- A child-to-child bond is precisely an actual paired leaf pair; no hidden
subtree or mere shape equivalence is substituted for its two endpoint leaves. -/
theorem paired_leaves_of_child_bond {w : ℕ} (G : Garden w) (b c : GBranch G.tree) (i j : Fin 3)
    (he : portMate G (.inr (b,i.succ)) = .inr (c,j.succ)) :
    ∃ ℓ q : GLeaf G.tree, ℓ.toNode = b.child i ∧ q.toNode = c.child j ∧ G.pair ℓ = q := by
  have hp : portMate G (encodeIncidence G (.inl (b.child i))) = encodeIncidence G (.inl (c.child j)) := by
    rw [encodeIncidence_child,encodeIncidence_child]
    exact he
  rw [portMate_encode] at hp
  change portEquiv G (incidenceMate G (.inl (b.child i))) = portEquiv G (.inl (c.child j)) at hp
  have hi := (portEquiv G).injective hp
  rcases (Comb.TreePath.mem_nodes_iff _ _).mp (b.child i).2 with hl | hb
  · let ℓ : GLeaf G.tree := ⟨(b.child i).1,hl⟩
    have hnode : b.child i = ℓ.toNode := Subtype.ext rfl
    rw [hnode,incidenceMate_leaf] at hi
    exact ⟨ℓ,G.pair ℓ,hnode.symm,Sum.inl.inj hi,rfl⟩
  · let d : GBranch G.tree := ⟨(b.child i).1,hb⟩
    have hnode : b.child i = d.toNode := Subtype.ext rfl
    rw [hnode,incidenceMate_branch] at hi
    cases hi

end WaveTurbulence.Reg.Skeleton
