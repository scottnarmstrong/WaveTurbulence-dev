/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceMiniClassification

/-! # Actual source subtrees of embedded A and B mini pieces -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Subtree extraction at an actual branching child composes with extraction at its parent. -/
theorem nodeSubtree_child {w : ℕ} (tree : Fin w → TTree) (b : GBranch tree) (i : Fin 3) :
    (Comb.nodeSubtree b.toNode).subtreeAt [i] = Comb.nodeSubtree (b.child i) := by
  have h := Comb.nodeSubtree_spec (b.child i)
  change Comb.subtree (tree b.1.1) (b.1.2 ++ [i]) = some (Comb.nodeSubtree (b.child i)) at h
  rw [Comb.subtree_append] at h
  have hs := Comb.nodeSubtree_spec b.toNode
  change Comb.subtree (tree b.1.1) b.1.2 = some (Comb.nodeSubtree b.toNode) at hs
  rw [hs] at h
  simp only [Option.bind_some] at h
  exact subtreeAt_eq_of_subtree _ _ _ h

/-- The full subtree at a branch is its three actual child subtrees. -/
theorem nodeSubtree_branch {w : ℕ} (tree : Fin w → TTree) (b : GBranch tree) :
    Comb.nodeSubtree b.toNode = node3 (fun i => Comb.nodeSubtree (b.child i)) := by
  have hb : [] ∈ (Comb.nodeSubtree b.toNode).branching :=
    (Comb.subtree_branching_iff (Comb.nodeSubtree_spec b.toNode) []).mpr
      (by rw [List.append_nil]; exact b.2)
  cases hs : Comb.nodeSubtree b.toNode with
  | leaf => simp [hs,TTree.branching] at hb
  | node l m r =>
    change node3 (fun i => (TTree.node l m r).subtreeAt [i]) = node3 (fun i => Comb.nodeSubtree (b.child i))
    apply congrArg node3
    funext i
    have he := nodeSubtree_child tree b i
    rw [hs] at he
    exact he

/-- An actual leaf has the trivial rooted subtree. -/
theorem nodeSubtree_leaf {w : ℕ} (tree : Fin w → TTree) (ℓ : GLeaf tree) :
    Comb.nodeSubtree ℓ.toNode = .leaf :=
  Option.some.inj ((Comb.nodeSubtree_spec ℓ.toNode).symm.trans (Comb.subtree_of_mem_leaves ℓ.2))

theorem LeafBond.left_subtree {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {i j : Fin 3}
    (h : LeafBond G b c i j) : Comb.nodeSubtree (b.child i) = .leaf := by
  obtain ⟨ℓ,q,hℓ,_,_⟩ := h
  rw [← hℓ]
  exact nodeSubtree_leaf G.tree ℓ

theorem LeafBond.right_subtree {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {i j : Fin 3}
    (h : LeafBond G b c i j) : Comb.nodeSubtree (c.child j) = .leaf := by
  obtain ⟨ℓ,q,_,hq,_⟩ := h
  rw [← hq]
  exact nodeSubtree_leaf G.tree q

theorem MiniAOccurrence.left_tree {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) : Comb.nodeSubtree b.toNode = .node .leaf .leaf .leaf := by
  rw [nodeSubtree_branch]
  have hs : ∀ i, Comb.nodeSubtree (b.child i) = .leaf := fun i => (h.2 i).left_subtree
  simp only [node3,hs]

theorem MiniAOccurrence.right_tree {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) : Comb.nodeSubtree c.toNode = .node .leaf .leaf .leaf := by
  rw [nodeSubtree_branch]
  have hs : ∀ i, Comb.nodeSubtree (c.child i) = .leaf := by
    intro i
    have hi : k.partner (k.partner i) = i := by fin_cases k <;> fin_cases i <;> decide
    have hp := (h.2 (k.partner i)).right_subtree
    rwa [hi] at hp
  simp only [node3,hs]

/-- The lower source branch has exactly its prescribed lone subtree and two side leaves. -/
theorem MiniBOccurrence.lower_tree {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) :
    Comb.nodeSubtree c.toNode = node3 (fun i => if i = m.lone then Comb.nodeSubtree (c.child m.lone) else .leaf) := by
  rw [nodeSubtree_branch]
  apply congrArg node3
  funext i
  by_cases hi : i = m.lone
  · subst i
    rw [ite_eq_left rfl]
  · rw [ite_eq_right hi]
    rcases miniTree_back_slots_cover m i hi with rfl | rfl
    · exact h.2.1.right_subtree
    · exact h.2.2.right_subtree

/-- Literal source B shape with the complete original lone-child subtree retained. -/
theorem MiniBOccurrence.upper_tree {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) :
    Comb.nodeSubtree b.toNode = node3 (fun i => if i = m.c then
      node3 (fun j => if j = m.lone then Comb.nodeSubtree (c.child m.lone) else .leaf) else .leaf) := by
  rw [nodeSubtree_branch]
  apply congrArg node3
  funext i
  by_cases hi : i = m.c
  · subst i
    rw [ite_eq_left rfl,h.1]
    exact h.lower_tree
  · rw [ite_eq_right hi]
    rcases miniTree_front_slots_cover m i hi with rfl | rfl
    · exact h.2.1.left_subtree
    · exact h.2.2.left_subtree

end WaveTurbulence.Reg.Skeleton
