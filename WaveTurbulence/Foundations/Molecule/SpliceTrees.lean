/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ExplicitRegions
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Subtrees
public import WaveTurbulence.Foundations.Molecule.GardenNodeCounts
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.ReplacementLeaves
import Mathlib.Tactic

/-! # The actual forest surgery underlying CL splicing
TARGET `block_clcn` (2): replace the upper subtree by a single ternary
vertex carrying the three retained boundary subtrees in their new slots.
The pairing and molecule equivalence are constructed separately.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- The actual subtree extracted at a valid forest node. -/
@[expose] noncomputable def spliceNodeSubtree (a : GNode G.tree) : TTree :=
  Classical.choose ((Comb.subtree_exists_iff (G.tree a.1.1) a.1.2).mpr a.2)

theorem spliceNodeSubtree_spec (a : GNode G.tree) :
    Comb.subtree (G.tree a.1.1) a.1.2 = some (spliceNodeSubtree G a) :=
  Classical.choose_spec ((Comb.subtree_exists_iff (G.tree a.1.1) a.1.2).mpr a.2)

/-- The new three-child subtree, using actual extracted old subtrees. -/
@[expose] noncomputable def spliceCrown (boundary : Fin 3 → GNode G.tree) : TTree :=
  .node (spliceNodeSubtree G (boundary 0)) (spliceNodeSubtree G (boundary 1)) (spliceNodeSubtree G (boundary 2))

/-- Replace the subtree at the upper CL joint, preserving all other trees. -/
@[expose] noncomputable def spliceForest (a : GBranch G.tree)
    (boundary : Fin 3 → GNode G.tree) : Fin w → TTree :=
  Function.update G.tree a.1.1
    (Comb.replaceAt (G.tree a.1.1) a.1.2 (spliceCrown G boundary))

theorem spliceForest_other (a : GBranch G.tree) (boundary : Fin 3 → GNode G.tree)
    (j : Fin w) (hj : j ≠ a.1.1) : spliceForest G a boundary j = G.tree j := by
  exact Function.update_of_ne hj _ _

theorem spliceForest_at (a : GBranch G.tree) (boundary : Fin 3 → GNode G.tree) :
    spliceForest G a boundary a.1.1 =
      Comb.replaceAt (G.tree a.1.1) a.1.2 (spliceCrown G boundary) := by
  exact Function.update_self _ _ _

/-- Exact leaf addresses in the changed tree; these are outside leaves
and leaves in the three transported boundary subtrees. -/
theorem spliceForest_leaves (a : GBranch G.tree) (boundary : Fin 3 → GNode G.tree) :
    (spliceForest G a boundary a.1.1).leaves =
      ((G.tree a.1.1).leaves.filter (fun q => ¬ a.1.2 <+: q)) ∪
        (spliceCrown G boundary).leaves.image (fun q => a.1.2++q) := by
  rw [spliceForest_at]
  exact Comb.leaves_replaceAt_eq (spliceNodeSubtree_spec G a.toNode) _

theorem spliceCrown_child_leaf (boundary : Fin 3 → GNode G.tree) (i : Fin 3) (q : Path) :
    i::q ∈ (spliceCrown G boundary).leaves ↔ q ∈ (spliceNodeSubtree G (boundary i)).leaves := by
  fin_cases i <;> simp [spliceCrown,TTree.leaves,TTree.cons_mem_pre]

end WaveTurbulence.Mole
