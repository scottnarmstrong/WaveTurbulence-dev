/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Replacement
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Structure

/-! # Subtree address transport (TARGET L627 and L845–L847) -/

public section

namespace WaveTurbulence.Comb
open TTree

/-- Leaf addresses transport exactly by prefixing the root address. -/
theorem subtree_leaves_iff : ∀ {t : TTree} {p : Path} {u : TTree},
    subtree t p = some u → ∀ q, q ∈ u.leaves ↔ p ++ q ∈ t.leaves
  | t, [], u, h, q => by
    have hu : t = u := by simpa [subtree] using h
    subst u
    rfl
  | .leaf, i :: p, u, h, q => by simp [subtree] at h
  | .node l m r, i :: p, u, h, q => by
    fin_cases i <;> simp [subtree] at h <;>
      simpa [List.cons_append, leaves, cons_mem_pre] using subtree_leaves_iff h q

/-- Branching-node addresses transport by the same prefix map. -/
theorem subtree_branching_iff : ∀ {t : TTree} {p : Path} {u : TTree},
    subtree t p = some u → ∀ q, q ∈ u.branching ↔ p ++ q ∈ t.branching
  | t, [], u, h, q => by
    have hu : t = u := by simpa [subtree] using h
    subst u
    rfl
  | .leaf, i :: p, u, h, q => by simp [subtree] at h
  | .node l m r, i :: p, u, h, q => by
    fin_cases i <;> simp [subtree] at h <;>
      simpa [List.cons_append, branching, cons_mem_pre] using subtree_branching_iff h q

/-- Node addresses transport by prefixing. -/
theorem subtree_nodes_iff {t u : TTree} {p : Path} (h : subtree t p = some u) (q : Path) :
    q ∈ u.nodes ↔ p ++ q ∈ t.nodes := by
  rw [TreePath.mem_nodes_iff, TreePath.mem_nodes_iff,
    subtree_leaves_iff h q, subtree_branching_iff h q]

/-- The actual embedding of a rooted subtree into a forest. -/
@[expose] def subtreeNodeEmbedding {w : ℕ} {tree : Fin w → TTree}
    (a : GNode tree) (u : TTree) (ha : subtree (tree a.1.1) a.1.2 = some u) :
    GNode (fun _ : Fin 1 => u) ↪ GNode tree where
  toFun q := ⟨(a.1.1, a.1.2 ++ q.1.2), (subtree_nodes_iff ha q.1.2).mp q.2⟩
  inj' := by
    intro q q' h
    apply Subtype.ext
    refine Prod.ext (Subsingleton.elim _ _) ?_
    have hh := congrArg (fun b => b.1.2) h
    exact List.append_cancel_left hh

/-- Restricting a decoration to a subtree preserves the branching sum rule. -/
theorem subtree_decoration_branching {w : ℕ} {tree : Fin w → TTree}
    {V : Type*} [AddCommGroup V] (κ : GNode tree → V)
    (hκ : ∀ b : GBranch tree, κ b.toNode = κ (b.child 0) - κ (b.child 1) + κ (b.child 2))
    (a : GNode tree) (u : TTree) (ha : subtree (tree a.1.1) a.1.2 = some u)
    (b : GBranch (fun _ : Fin 1 => u)) :
    κ (subtreeNodeEmbedding a u ha b.toNode) =
      κ (subtreeNodeEmbedding a u ha (b.child 0)) -
        κ (subtreeNodeEmbedding a u ha (b.child 1)) +
          κ (subtreeNodeEmbedding a u ha (b.child 2)) := by
  let b' : GBranch tree :=
    ⟨(a.1.1, a.1.2 ++ b.1.2), (subtree_branching_iff ha b.1.2).mp b.2⟩
  have hr : subtreeNodeEmbedding a u ha b.toNode = b'.toNode := by
    apply Subtype.ext
    rfl
  have he (i : Fin 3) : subtreeNodeEmbedding a u ha (b.child i) = b'.child i := by
    apply Subtype.ext
    change (a.1.1, a.1.2 ++ (b.1.2 ++ [i])) = (a.1.1, (a.1.2 ++ b.1.2) ++ [i])
    rw [List.append_assoc]
  rw [hr, he 0, he 1, he 2]
  exact hκ b' 

/-- Restricting a layering to a subtree preserves child monotonicity (TARGET L650). -/
theorem subtree_layering_branching {w : ℕ} (LG : LayeredGarden w)
    (a : GNode LG.garden.tree) (u : TTree)
    (ha : subtree (LG.garden.tree a.1.1) a.1.2 = some u)
    (b : GBranch (fun _ : Fin 1 => u)) (i : Fin 3) :
    LG.layer (subtreeNodeEmbedding a u ha (b.child i)) ≤
      LG.layer (subtreeNodeEmbedding a u ha b.toNode) := by
  let b' : GBranch LG.garden.tree :=
    ⟨(a.1.1, a.1.2 ++ b.1.2), (subtree_branching_iff ha b.1.2).mp b.2⟩
  have hr : subtreeNodeEmbedding a u ha b.toNode = b'.toNode := by
    apply Subtype.ext
    rfl
  have he : subtreeNodeEmbedding a u ha (b.child i) = b'.child i := by
    apply Subtype.ext
    change (a.1.1, a.1.2 ++ (b.1.2 ++ [i])) = (a.1.1, (a.1.2 ++ b.1.2) ++ [i])
    rw [List.append_assoc]
  rw [hr, he]
  exact LG.isLayering.1 b' i 

end WaveTurbulence.Comb
