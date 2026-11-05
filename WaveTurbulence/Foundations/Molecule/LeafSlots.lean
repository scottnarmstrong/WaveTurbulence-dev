/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegionIncidences
import Mathlib.Tactic

/-! # A leaf child slot is internal exactly when its actual LP bond is internal
TARGET `block_clcn`, complete pairing of the realization leaves.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem leaf_slot_internal_iff (S : Finset (GBranch G.tree))
    (l : GLeaf G.tree) (hn : l.1.2 ≠ []) :
    (l.1.2.getLast hn).succ ∈ internalPositions G S (GNode.parent l.toNode hn) ↔
      IsInternalLeaf G S l := by
  constructor
  · intro hi
    obtain ⟨x,hx,hg,hpi⟩ := (mem_internalPositions G).mp hi
    have hslot := slotNode_dart G x
    rw [hx,hpi] at hslot
    have he : slotNode G (GNode.parent l.toNode hn) (l.1.2.getLast hn).succ = l.toNode :=
      parent_child_eq_node l.toNode hn
    have hnode : dartNode G x = l.toNode := hslot.symm.trans he
    rcases x with ⟨c,b⟩ | k
    · exact (branch_toNode_ne_leaf c.1 l hnode).elim
    · have heq : k.1 = l := leaf_toNode_injective hnode
      subst l
      exact ⟨k.2.1,k.2.2.1,k.2.2.2,hg⟩
  · rintro ⟨hm,hln,hp,hg⟩
    exact (mem_internalPositions G).mpr ⟨.inr ⟨l,hm,hln,hp⟩,rfl,hg,rfl⟩

end WaveTurbulence.Mole
