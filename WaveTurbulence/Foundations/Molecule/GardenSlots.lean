/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenLabelExtension
public import WaveTurbulence.Foundations.Molecule.GardenOrientation
import Mathlib.Tactic

/-! # Four-node incidence slots used by the decoration correspondence -/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} (G : Garden w)

/-- Parent slot zero followed by left, middle and right child slots. -/
@[expose] def slotNode (v : GBranch G.tree) (i : Fin 4) : GNode G.tree :=
  Fin.cases v.toNode (fun j => v.child j) i

theorem slotNode_dart (x : GardenDart G) :
    slotNode G (G.molecule.atom x) (dartPosition G x) = dartNode G x := by
  rcases x with ⟨c,b⟩ | l
  · cases b
    · rfl
    · exact parent_child_eq_node c.1.toNode c.2
  · exact parent_child_eq_node l.1.toNode l.2.2.1

theorem child_nonroot (v : GBranch G.tree) (i : Fin 3) : (v.child i).1.2 ≠ [] := by
  exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

/-- Every nonroot branching-node slot is occupied by a PC dart. -/
theorem branch_slot_occupied (v : GBranch G.tree) (i : Fin 4)
    (hb : (slotNode G v i).1.2 ∈ (G.tree (slotNode G v i).1.1).branching)
    (hr : (slotNode G v i).1.2 ≠ []) :
    ∃ x : GardenDart G, G.molecule.atom x = v ∧ dartPosition G x = i := by
  revert hb hr
  refine Fin.cases ?_ (fun j => ?_) i
  · intro _hb hr
    refine ⟨.inl (⟨v,hr⟩,false),rfl,rfl⟩
  · intro hb hr
    let b : GBranch G.tree := ⟨(v.child j).1,hb⟩
    refine ⟨.inl (⟨b,hr⟩,true),?_,?_⟩
    · apply Subtype.ext
      simp only [Garden.molecule,GNode.parent,b,GBranch.child,GBranch.toNode,
        List.dropLast_append_cons,List.dropLast_singleton,List.append_nil]
    · change ((v.1.2++[j]).getLast hr).succ = j.succ
      rw [List.getLast_append_singleton]

/-- Every leaf slot whose partner is also nonroot is occupied by an LP dart. -/
theorem leaf_slot_occupied (hP : G.IsPlain) (v : GBranch G.tree) (i : Fin 3)
    (hl : (v.child i).1.2 ∈ (G.tree (v.child i).1.1).leaves)
    (hp : (G.pair ⟨(v.child i).1,hl⟩).1.2 ≠ []) :
    ∃ x : GardenDart G, G.molecule.atom x = v ∧ dartPosition G x = i.succ := by
  let l : GLeaf G.tree := ⟨(v.child i).1,hl⟩
  refine ⟨.inr ⟨l,hP l,child_nonroot G v i,hp⟩,?_,?_⟩
  · apply Subtype.ext
    simp only [Garden.molecule,GNode.parent,l,GLeaf.toNode,GBranch.child,
      List.dropLast_append_cons,List.dropLast_singleton,List.append_nil]
  · change ((v.1.2++[i]).getLast (child_nonroot G v i)).succ = i.succ
    rw [List.getLast_append_singleton]

/-- Actual slots missing from the molecule are boundary data: their labels
are determined entirely by the prescribed roots. -/
theorem missing_slot_fixed {E : Type*} (hP : G.IsPlain) (n : Fin w → E)
    (k k' : GardenDart G → E) (v : GBranch G.tree) (i : Fin 4)
    (hi : ¬ ∃ x : GardenDart G, G.molecule.atom x = v ∧ dartPosition G x = i) :
    extendLabels G hP n k (slotNode G v i) =
      extendLabels G hP n k' (slotNode G v i) := by
  revert hi
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hi
    by_cases hr : v.1.2 = []
    · have he : v.toNode = GNode.root G.tree v.1.1 := Subtype.ext (Prod.ext rfl hr)
      change extendLabels G hP n k v.toNode = extendLabels G hP n k' v.toNode
      rw [he,extendLabels_root,extendLabels_root]
    · exact (hi (branch_slot_occupied G v 0 v.2 hr)).elim
  · intro hi
    let a := v.child j
    have hr := child_nonroot G v j
    by_cases hb : a.1.2 ∈ (G.tree a.1.1).branching
    · exact (hi (branch_slot_occupied G v j.succ hb hr)).elim
    · have hl := ((TTree.mem_nodes_iff _ _).mp a.2).resolve_right hb
      let l : GLeaf G.tree := ⟨a.1,hl⟩
      have hp : (G.pair l).1.2 = [] := by
        by_contra hp
        exact hi (leaf_slot_occupied G hP v j hl hp)
      exact (extendLabels_leaf_paired_root G hP n k l hr hp).trans
        (extendLabels_leaf_paired_root G hP n k' l hr hp).symm

end WaveTurbulence.Mole
