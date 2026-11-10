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

end WaveTurbulence.Comb
