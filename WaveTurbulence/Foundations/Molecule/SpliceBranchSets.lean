/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SpliceTrees
import Mathlib.Tactic

/-! # Exact branching-address surgery for CL splicing
TARGET `block_clcn` (2). Adapted from COMB-CORE's proved leaf-address
replacement identity, with branching nodes including the retained crown root.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset Comb
variable {w : ℕ} (G : Garden w)

theorem branching_replaceAt_eq : ∀ {t : TTree} {p : Path} {u : TTree},
    subtree t p = some u → ∀ s : TTree,
      (replaceAt t p s).branching =
        (t.branching.filter (fun q => ¬ p <+: q)) ∪ s.branching.image (fun q => p ++ q)
  | t, [], u, h, s => by simp [replaceAt]
  | .leaf, i :: p, u, h, s => by simp [subtree] at h
  | .node l m r, i :: p, u, h, s => by
    fin_cases i <;> simp [subtree] at h
    all_goals
      ext q
      cases q with
      | nil => simp [replaceAt,branching,nil_notMem_pre]
      | cons j q =>
        fin_cases j <;>
          simp [replaceAt,branching,cons_mem_pre,List.cons_prefix_cons,
            Finset.mem_image,List.cons_append,List.cons.injEq,branching_replaceAt_eq h]

theorem spliceForest_branching (a : GBranch G.tree) (boundary : Fin 3 → GNode G.tree) :
    (spliceForest G a boundary a.1.1).branching =
      ((G.tree a.1.1).branching.filter (fun q => ¬ a.1.2 <+: q)) ∪
        (spliceCrown G boundary).branching.image (fun q => a.1.2++q) := by
  rw [spliceForest_at]
  exact branching_replaceAt_eq (spliceNodeSubtree_spec G a.toNode) _

theorem spliceCrown_child_branch (boundary : Fin 3 → GNode G.tree) (i : Fin 3) (q : Path) :
    i::q ∈ (spliceCrown G boundary).branching ↔ q ∈ (spliceNodeSubtree G (boundary i)).branching := by
  fin_cases i <;> simp [spliceCrown,TTree.branching,TTree.cons_mem_pre]

end WaveTurbulence.Mole
