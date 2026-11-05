/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockTypes
public import WaveTurbulence.Foundations.Molecule.PortShim
import Mathlib.Tactic

/-! # Branch and paired-leaf membership from actual internal incidences
TARGET `block_clcn`: PC positions detect selected children; LP positions
give paired leaves in the realization without any assumed pairing closure.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- The slot of a branching child is internal exactly when the child is selected. -/
theorem parent_child_slot_internal_iff (S : Finset (GBranch G.tree))
    (b : GBranch G.tree) (hn : b.1.2 ≠ [])
    (hp : GNode.parent b.toNode hn ∈ S) :
    (b.1.2.getLast hn).succ ∈ internalPositions G S (GNode.parent b.toNode hn) ↔ b ∈ S := by
  let z : GardenDart G := .inl (⟨b,hn⟩,true)
  have hz : G.molecule.atom z = GNode.parent b.toNode hn := rfl
  have hpos : dartPosition G z = (b.1.2.getLast hn).succ := rfl
  constructor
  · intro hi
    obtain ⟨x,hx,hg,hpi⟩ := (mem_internalPositions G).mp hi
    have he : x = z := atom_position_injective G (Prod.ext (hx.trans hz.symm) (hpi.trans hpos.symm))
    subst x
    exact hg.2
  · intro hb
    exact (mem_internalPositions G).mpr ⟨z,hz,⟨hp,hb⟩,hpos⟩

/-- Leaves carried by the actual internal LP bonds. -/
@[expose] def IsInternalLeaf (S : Finset (GBranch G.tree)) (l : GLeaf G.tree) : Prop :=
  ∃ (hm : G.mark l = none) (hn : l.1.2 ≠ []) (hp : (G.pair l).1.2 ≠ []),
    G.molecule.InGroup S (.inr ⟨l,hm,hn,hp⟩)

theorem internal_leaf_pair_iff (S : Finset (GBranch G.tree)) (l : GLeaf G.tree) :
    IsInternalLeaf G S (G.pair l) ↔ IsInternalLeaf G S l := by
  have hforward : ∀ l, IsInternalLeaf G S l → IsInternalLeaf G S (G.pair l) := by
    intro l hl
    obtain ⟨hm,hn,hp,hg⟩ := hl
    refine ⟨Garden.pair_unmarked hm,hp,by simpa only [G.pair_pair] using hn,?_⟩
    exact ⟨hg.2,by simpa only [Garden.molecule,G.pair_pair] using hg.1⟩
  exact ⟨fun h => by simpa only [G.pair_pair] using hforward (G.pair l) h,hforward l⟩

theorem internal_leaf_unmarked {S : Finset (GBranch G.tree)} {l : GLeaf G.tree}
    (hl : IsInternalLeaf G S l) : G.mark l = none := by
  obtain ⟨hm,_⟩ := hl
  exact hm

/-- Intrinsic realization, recording the actual branches and the actual internal LP leaves.
Its descendant-set description is proved separately from incidence membership. -/
@[expose] def InIncidenceRealization (S : Finset (GBranch G.tree)) (a : GNode G.tree) : Prop :=
  (∃ b ∈ S, b.toNode = a) ∨ ∃ l, IsInternalLeaf G S l ∧ l.toNode = a

theorem branch_incidence_realization_iff (S : Finset (GBranch G.tree)) (b : GBranch G.tree) :
    InIncidenceRealization G S b.toNode ↔ b ∈ S := by
  constructor
  · rintro (⟨c,hc,he⟩ | ⟨l,_hl,he⟩)
    · exact branch_toNode_injective he ▸ hc
    · exact (branch_toNode_ne_leaf b l he.symm).elim
  · intro hb
    exact Or.inl ⟨b,hb,rfl⟩

theorem leaf_incidence_realization_iff (S : Finset (GBranch G.tree)) (l : GLeaf G.tree) :
    InIncidenceRealization G S l.toNode ↔ IsInternalLeaf G S l := by
  constructor
  · rintro (⟨b,_hb,he⟩ | ⟨k,hk,he⟩)
    · exact (branch_toNode_ne_leaf b l he).elim
    · exact leaf_toNode_injective he ▸ hk
  · intro hl
    exact Or.inr ⟨l,hl,rfl⟩

/-- Pairing closure is a theorem about the actual garden involution. -/
theorem incidence_realization_leaf_pair (S : Finset (GBranch G.tree)) (l : GLeaf G.tree) :
    InIncidenceRealization G S (G.pair l).toNode ↔ InIncidenceRealization G S l.toNode := by
  rw [leaf_incidence_realization_iff,leaf_incidence_realization_iff,internal_leaf_pair_iff]

end WaveTurbulence.Mole
