/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedPairedTree

/-! # Grafting and inverse collapse identities (TARGET L846–L847) -/

public section

namespace WaveTurbulence.Comb
open TTree

/-- Replacing twice at one valid address keeps only the final inserted subtree. -/
theorem replaceAt_replaceAt : ∀ {t : TTree} {p : Path} {u : TTree},
    subtree t p = some u → ∀ s r, replaceAt (replaceAt t p s) p r = replaceAt t p r
  | t, [], u, h, s, r => by simp [replaceAt]
  | .leaf, i :: p, u, h, s, r => by simp [subtree] at h
  | .node l m r₀, i :: p, u, h, s, r => by
    fin_cases i <;> simp [subtree] at h <;>
      simp [replaceAt, replaceAt_replaceAt h]

/-- Grafting the removed subtree into the new leaf reverses collapse. -/
theorem graft_collapse_eq {t u : TTree} {p : Path} (h : subtree t p = some u) :
    replaceAt (collapseAt t p) p u = t := by
  rw [collapseAt, replaceAt_replaceAt h, replaceAt_self h]

/-- Extracting a leaf gives the trivial subtree. -/
theorem subtree_of_mem_leaves : ∀ {t : TTree} {p : Path}, p ∈ t.leaves → subtree t p = some .leaf
  | .leaf, p, h => by
    have hp : p = [] := Finset.mem_singleton.mp h
    subst p
    simp [subtree]
  | .node l m r, [], h => by simp [leaves, nil_notMem_pre] at h
  | .node l m r, i :: p, h => by
    fin_cases i <;> simp [leaves, cons_mem_pre] at h <;>
      simp [subtree, subtree_of_mem_leaves h]

/-- Grafting into a leaf adds orders (TARGET replacement of a node by a paired tree). -/
theorem order_graft_leaf {t : TTree} {p : Path} (h : p ∈ t.leaves) (s : TTree) :
    (replaceAt t p s).order = t.order + s.order := by
  simpa only [order, Nat.add_zero] using order_replaceAt (subtree_of_mem_leaves h) s

end WaveTurbulence.Comb
