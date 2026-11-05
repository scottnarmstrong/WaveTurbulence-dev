/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-!
# The branching nodes of a ternary tree

For the B̃ bridge (DH21 (defcoefb2), (deftildeb); DH23 L951–L956): the branching nodes `TB T` of one
Wave B tree, the splitting `TB (node l m r) ≃ Unit ⊕ (TB l ⊕ (TB m ⊕ TB r))` (root and the three
subtrees), and the ancestors of a branching node.
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree

/-- The children of a node, `![l, m, r]`; a leaf has no children (junk `leaf`). -/
def tchild : TTree → Fin 3 → TTree
  | .leaf, _ => .leaf
  | .node l m r, i => ![l, m, r] i

/-- The branching nodes of one tree. -/
abbrev TB (T : TTree) : Type := {p : TTree.Path // p ∈ T.branching}

theorem branching_leaf : TTree.leaf.branching = ∅ := rfl

theorem nil_mem_branching_node (l m r : TTree) : ([] : TTree.Path) ∈ (TTree.node l m r).branching := by
  simp [TTree.branching]

theorem cons_mem_branching_node (l m r : TTree) (i : Fin 3) (q : TTree.Path) :
    i :: q ∈ (TTree.node l m r).branching ↔ q ∈ (tchild (TTree.node l m r) i).branching := by
  simp only [TTree.branching, TTree.pre, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    List.cons.injEq, reduceCtorEq, false_or, tchild]
  fin_cases i <;> simp

theorem not_mem_branching_leaf (p : TTree.Path) : p ∉ TTree.leaf.branching := by
  simp [TTree.branching]

/-- The parent of a branching node is a branching node. -/
theorem mem_branching_of_append : ∀ (T : TTree) (p : TTree.Path) (i : Fin 3),
    p ++ [i] ∈ T.branching → p ∈ T.branching
  | .leaf, p, i, h => absurd h (not_mem_branching_leaf _)
  | .node l m r, [], i, _ => nil_mem_branching_node l m r
  | .node l m r, j :: p, i, h => by
    rw [List.cons_append, cons_mem_branching_node] at h
    rw [cons_mem_branching_node]
    cases hc : tchild (TTree.node l m r) j with
    | leaf => rw [hc] at h; exact absurd h (not_mem_branching_leaf _)
    | node a b c =>
      rw [hc] at h
      exact mem_branching_of_append _ p i h

/-- The root of a node tree. -/
def TB.root (l m r : TTree) : TB (.node l m r) := ⟨[], nil_mem_branching_node l m r⟩

/-- The embedding of the branching nodes of the `i`-th subtree. -/
def TB.sub (l m r : TTree) (i : Fin 3) (q : TB (tchild (TTree.node l m r) i)) :
    TB (.node l m r) :=
  ⟨i :: q.1, (cons_mem_branching_node l m r i q.1).2 q.2⟩

/-- The restriction of node times to the `i`-th subtree. -/
def restrT {l m r : TTree} (i : Fin 3) (τ : TB (.node l m r) → ℝ) :
    TB (tchild (TTree.node l m r) i) → ℝ :=
  fun q => τ (TB.sub l m r i q)

/-- **The splitting of the branching nodes of a node tree.** -/
def tbNodeEquiv (l m r : TTree) : TB (.node l m r) ≃ Unit ⊕ (TB l ⊕ (TB m ⊕ TB r)) where
  toFun p := match p with
    | ⟨[], _⟩ => .inl ()
    | ⟨i :: q, h⟩ =>
      if h0 : i = 0 then .inr (.inl ⟨q, by
        have := (cons_mem_branching_node l m r i q).1 h; subst h0; simpa [tchild] using this⟩)
      else if h1 : i = 1 then .inr (.inr (.inl ⟨q, by
        have := (cons_mem_branching_node l m r i q).1 h; subst h1; simpa [tchild] using this⟩))
      else .inr (.inr (.inr ⟨q, by
        have := (cons_mem_branching_node l m r i q).1 h
        have h2 : i = 2 := by omega
        subst h2; simpa [tchild] using this⟩))
  invFun x := match x with
    | .inl () => TB.root l m r
    | .inr (.inl q) => ⟨0 :: q.1, (cons_mem_branching_node l m r 0 q.1).2 (by simp [tchild])⟩
    | .inr (.inr (.inl q)) => ⟨1 :: q.1, (cons_mem_branching_node l m r 1 q.1).2 (by simp [tchild])⟩
    | .inr (.inr (.inr q)) => ⟨2 :: q.1, (cons_mem_branching_node l m r 2 q.1).2 (by simp [tchild])⟩
  left_inv p := by
    rcases p with ⟨_ | ⟨i, q⟩, h⟩
    · rfl
    · fin_cases i <;> rfl
  right_inv x := by
    rcases x with ⟨⟩ | q | q | q <;> rfl

end WaveTurbulence.MainCoef
