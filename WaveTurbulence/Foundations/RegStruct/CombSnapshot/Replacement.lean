/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Trees

/-! # Subtrees, replacement and collapse (TARGET embedded objects, L845–L847)

An invalid address returns `none` for extraction and leaves the tree unchanged
under replacement. Every source-facing identity explicitly uses a valid address.
-/

public section

namespace WaveTurbulence.Comb
open TTree

/-- Extract the subtree at an address; invalid addresses have no subtree. -/
@[expose] def subtree : TTree → Path → Option TTree
  | t, [] => some t
  | .leaf, _ :: _ => none
  | .node l m r, i :: p => if i = 0 then subtree l p else if i = 1 then subtree m p else subtree r p

/-- Replace one rooted subtree. Invalid addresses leave the tree unchanged. -/
@[expose] def replaceAt : TTree → Path → TTree → TTree
  | _, [], s => s
  | .leaf, _ :: _, _ => .leaf
  | .node l m r, i :: p, s =>
    if i = 0 then .node (replaceAt l p s) m r
    else if i = 1 then .node l (replaceAt m p s) r
    else .node l m (replaceAt r p s)

/-- Collapsing a subtree replaces it by a single leaf. -/
@[expose] def collapseAt (t : TTree) (p : Path) : TTree := replaceAt t p .leaf

/-- Extraction exists exactly at the tree's node addresses. -/
theorem subtree_exists_iff : ∀ (t : TTree) (p : Path),
    (∃ s, subtree t p = some s) ↔ p ∈ t.nodes
  | t, [] => by cases t <;> simp [subtree, nodes]
  | .leaf, i :: p => by simp [subtree, nodes]
  | .node l m r, i :: p => by
    fin_cases i <;> simp [subtree, nodes, cons_mem_pre, subtree_exists_iff]

/-- Subtree extraction composes along concatenated paths. -/
theorem subtree_append : ∀ (t : TTree) (p q : Path),
    subtree t (p ++ q) = (subtree t p).bind (fun s => subtree s q)
  | t, [], q => by simp [subtree]
  | .leaf, i :: p, q => by simp [subtree]
  | .node l m r, i :: p, q => by
    fin_cases i <;> simp [subtree, subtree_append]

/-- Replacing at a valid address makes the inserted tree its subtree. -/
theorem subtree_replaceAt : ∀ {t : TTree} {p : Path} {u : TTree},
    subtree t p = some u → ∀ s, subtree (replaceAt t p s) p = some s
  | t, [], u, h, s => by simp [replaceAt, subtree]
  | .leaf, i :: p, u, h, s => by simp [subtree] at h
  | .node l m r, i :: p, u, h, s => by
    fin_cases i <;> simp [subtree, replaceAt] at h ⊢ <;>
      exact subtree_replaceAt h s

/-- Replacement by the original subtree is the identity. -/
theorem replaceAt_self : ∀ {t : TTree} {p : Path} {u : TTree},
    subtree t p = some u → replaceAt t p u = t
  | t, [], u, h => by
    have hu : t = u := by simpa [subtree] using h
    subst u
    simp [replaceAt]
  | .leaf, i :: p, u, h => by simp [subtree] at h
  | .node l m r, i :: p, u, h => by
    fin_cases i <;> simp [subtree, replaceAt] at h ⊢ <;>
      rw [replaceAt_self h]

/-- Replacement adds precisely the inserted order minus the removed order. -/
theorem order_replaceAt : ∀ {t : TTree} {p : Path} {u : TTree},
    subtree t p = some u → ∀ s, (replaceAt t p s).order + u.order = t.order + s.order
  | t, [], u, h, s => by
    have hu : t = u := by simpa [subtree] using h
    subst u
    simp only [replaceAt]
    omega
  | .leaf, i :: p, u, h, s => by simp [subtree] at h
  | .node l m r, i :: p, u, h, s => by
    fin_cases i <;> simp [subtree, replaceAt] at h ⊢
    · have hi := order_replaceAt h s
      simp only [order] at ⊢
      omega
    · have hi := order_replaceAt h s
      simp only [order] at ⊢
      omega
    · have hi := order_replaceAt h s
      simp only [order] at ⊢
      omega

end WaveTurbulence.Comb
