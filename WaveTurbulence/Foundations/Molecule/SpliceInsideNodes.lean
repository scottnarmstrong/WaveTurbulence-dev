/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLBranchNames
import Mathlib.Tactic

/-! # Parent addresses inside transported boundary subtrees -/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {G : Garden w} {a : GBranch G.tree} (B : SpliceBoundaryRoots G a)

@[expose] def spliceOldInsideNode (i : Fin 3) (q : Path)
    (hq : q ∈ (spliceNodeSubtree G (B.node i)).nodes) : GNode G.tree :=
  ⟨((B.node i).1.1,(B.node i).1.2++q),
    (Comb.subtree_nodes_iff (spliceNodeSubtree_spec G (B.node i)) q).mp hq⟩

@[expose] def spliceNewInsideNode (i : Fin 3) (q : Path)
    (hq : q ∈ (spliceNodeSubtree G (B.node i)).nodes) : GNode (spliceForest G a B.node) :=
  ⟨(a.1.1,a.1.2++i::q),by
    rw [spliceForest_at]
    have hs := Comb.subtree_replaceAt (spliceNodeSubtree_spec G a.toNode) (spliceCrown G B.node)
    apply (Comb.subtree_nodes_iff hs (i::q)).mp
    fin_cases i <;> simp [spliceCrown,TTree.nodes,TTree.cons_mem_pre]
    all_goals exact hq⟩

theorem parent_spliceNewInside_nil (i : Fin 3)
    (hq : ([] : Path) ∈ (spliceNodeSubtree G (B.node i)).nodes)
    (hn : (spliceNewInsideNode B i [] hq).1.2 ≠ []) :
    GNode.parent (spliceNewInsideNode B i [] hq) hn = spliceCrownBranch B := by
  apply Subtype.ext
  exact Prod.ext rfl (by
    change (a.1.2++[i]).dropLast = a.1.2
    rw [List.dropLast_append_cons,List.dropLast_singleton,List.append_nil])

theorem parent_spliceNewInside_nonempty (i : Fin 3) (q : Path)
    (hq : q ∈ (spliceNodeSubtree G (B.node i)).nodes) (hqne : q ≠ [])
    (hn : (spliceNewInsideNode B i q hq).1.2 ≠ []) :
    GNode.parent (spliceNewInsideNode B i q hq) hn =
      spliceBranchPieceNew B (.inr ⟨i,⟨q.dropLast,TTree.dropLast_mem_branching hq hqne⟩⟩) := by
  apply Subtype.ext
  exact Prod.ext rfl (by
    change (a.1.2++i::q).dropLast = a.1.2++i::q.dropLast
    rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _),List.dropLast_cons_of_ne_nil hqne])

theorem parent_spliceOldInside_nonempty (i : Fin 3) (q : Path)
    (hq : q ∈ (spliceNodeSubtree G (B.node i)).nodes) (hqne : q ≠ [])
    (hn : (spliceOldInsideNode B i q hq).1.2 ≠ []) :
    GNode.parent (spliceOldInsideNode B i q hq) hn =
      spliceBranchPieceOld B (.inr ⟨i,⟨q.dropLast,TTree.dropLast_mem_branching hq hqne⟩⟩) := by
  apply Subtype.ext
  exact Prod.ext rfl (by
    change ((B.node i).1.2++q).dropLast = (B.node i).1.2++q.dropLast
    rw [List.dropLast_append_of_ne_nil hqne])

end WaveTurbulence.Mole
