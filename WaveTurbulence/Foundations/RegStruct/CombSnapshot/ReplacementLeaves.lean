/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Replacement

/-! # Exact leaf addresses after replacement and collapse (TARGET L846) -/

public section

namespace WaveTurbulence.Comb
open TTree Finset

/-- Exact leaf-set surgery for replacing a rooted subtree. -/
theorem leaves_replaceAt_eq : ∀ {t : TTree} {p : Path} {u : TTree},
    subtree t p = some u → ∀ s : TTree,
      (replaceAt t p s).leaves =
        (t.leaves.filter (fun q => ¬ p <+: q)) ∪ s.leaves.image (fun q => p ++ q)
  | t, [], u, h, s => by simp [replaceAt]
  | .leaf, i :: p, u, h, s => by simp [subtree] at h
  | .node l m r, i :: p, u, h, s => by
    fin_cases i <;> simp [subtree] at h
    all_goals
      ext q
      cases q with
      | nil => simp [replaceAt, leaves, nil_notMem_pre]
      | cons j q =>
        fin_cases j <;>
          simp [replaceAt, leaves, cons_mem_pre, List.cons_prefix_cons,
            Finset.mem_image, List.cons_append, List.cons.injEq, leaves_replaceAt_eq h]

/-- Collapsing replaces the lower subtree's leaves by its root address. -/
theorem leaves_collapseAt_eq {t u : TTree} {p : Path} (h : subtree t p = some u) :
    (collapseAt t p).leaves = (t.leaves.filter (fun q => ¬ p <+: q)) ∪ {p} := by
  simpa [collapseAt, leaves] using leaves_replaceAt_eq h .leaf

/-- The collapsed node becomes a leaf, including when the collapse is at the root. -/
theorem mem_leaves_collapseAt {t u : TTree} {p : Path} (h : subtree t p = some u) :
    p ∈ (collapseAt t p).leaves := by
  rw [leaves_collapseAt_eq h]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- Every other collapsed-tree leaf is an old leaf outside the removed subtree. -/
theorem mem_leaves_collapseAt_iff {t u : TTree} {p q : Path} (h : subtree t p = some u) :
    q ∈ (collapseAt t p).leaves ↔ (q ∈ t.leaves ∧ ¬ p <+: q) ∨ q = p := by
  rw [leaves_collapseAt_eq h]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]

end WaveTurbulence.Comb
