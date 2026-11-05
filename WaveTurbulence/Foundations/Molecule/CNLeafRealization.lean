/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CNBranchRealization
public import WaveTurbulence.Foundations.Molecule.CLLeafRealization
import Mathlib.Tactic

/-! # Exact CN realization and complete leaf pairing
TARGET `block_clcn` (CN)(iii), including nested-joint configurations.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem joint_pruned_child_extension {S : Finset (GBranch G.tree)} {a p : GBranch G.tree}
    (hp : InJointPrunedRegion G S a p.toNode) (i : Fin 3)
    (hi : i.succ ∈ internalPositions G S p) : InJointPrunedRegion G S a (p.child i) := by
  refine ⟨⟨hp.1.1,hp.1.2.trans (List.prefix_append _ _)⟩,?_⟩
  intro k hk
  exact excluded_child_extension G hk hi (hp.2 k hk)

theorem joint_pruned_leaf_internal {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hb : ¬ InternalParent G S b)
    (l : GLeaf G.tree) (hl : InJointPrunedRegion G S a l.toNode) : IsInternalLeaf G S l := by
  classical
  have hne : l.toNode ≠ a.toNode := (branch_toNode_ne_leaf a l).symm
  have hn : l.1.2 ≠ [] := by
    intro hn
    have ha : a.1.2 = [] := List.prefix_nil.mp (hn ▸ hl.1.2)
    exact hne (Subtype.ext (Prod.ext hl.1.1.symm (hn.trans ha.symm)))
  let p := GNode.parent l.toNode hn
  have hpregion : InJointPrunedRegion G S a p.toNode := by
    refine ⟨⟨hl.1.1,proper_prefix_dropLast hl.1.2 ?_⟩,?_⟩
    · intro he
      exact hne (Subtype.ext (Prod.ext hl.1.1.symm he.symm))
    · intro i hi hd
      exact hl.2 i hi ⟨hd.1,hd.2.trans (List.dropLast_prefix _)⟩
  have hp := joint_pruned_branch_mem_of_other_parent_outside G hB hb p hpregion
  apply (leaf_slot_internal_iff G S l hn).mp
  by_contra hm
  by_cases hpa : p = a
  · have hd : (p.child (l.1.2.getLast hn)).IsDesc l.toNode := by
      refine ⟨rfl,?_⟩
      change (l.1.2.dropLast++[l.1.2.getLast hn]) <+: l.1.2
      rw [List.dropLast_append_getLast]
    exact hl.2 _ (hpa ▸ hm) (hpa ▸ hd)
  have hpb : p ≠ b := by
    intro he
    exact cn_other_joint_not_pruned G hB hb (he ▸ hpregion)
  have hf := full_internalPositions G (hB.2.2.2.2.2.2.2.2.1 p hp hpa hpb)
  change (l.1.2.getLast hn).succ ∉ internalPositions G S p at hm
  rw [hf] at hm
  exact hm (mem_univ _)

/-- Exact CN leaf membership in the union of the two pruned subtrees. -/
theorem cn_leaf_realization_iff {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCN : CNParentPattern G S a b) (l : GLeaf G.tree) :
    IsInternalLeaf G S l ↔ InJointPrunedRegion G S a l.toNode ∨ InJointPrunedRegion G S b l.toNode := by
  constructor
  · rintro ⟨hm,hn,hpair,hg⟩
    have hp : GNode.parent l.toNode hn ∈ S := hg.1
    have hi := (leaf_slot_internal_iff G S l hn).mpr ⟨hm,hn,hpair,hg⟩
    have he := parent_child_eq_node (tree := G.tree) l.toNode hn
    rcases selected_branch_below_pruned_joint G hB _ hp with ha | hb
    · exact Or.inl (he ▸ joint_pruned_child_extension G ha _ hi)
    · exact Or.inr (he ▸ joint_pruned_child_extension G hb _ hi)
  · rintro (ha | hb)
    · exact joint_pruned_leaf_internal G hB hCN.2 l ha
    · exact joint_pruned_leaf_internal G (block_swap_joints G.molecule hB) hCN.1 l hb

/-- The full actual CN realization equals the source's union of two pruned subtrees. -/
theorem cn_node_realization_iff {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCN : CNParentPattern G S a b) (v : GNode G.tree) :
    InIncidenceRealization G S v ↔ InJointPrunedRegion G S a v ∨ InJointPrunedRegion G S b v := by
  rcases (TTree.mem_nodes_iff _ _).mp v.2 with hl | hb
  · let l : GLeaf G.tree := ⟨v.1,hl⟩
    change InIncidenceRealization G S l.toNode ↔
      InJointPrunedRegion G S a l.toNode ∨ InJointPrunedRegion G S b l.toNode
    rw [leaf_incidence_realization_iff,cn_leaf_realization_iff G hB hCN]
  · let c : GBranch G.tree := ⟨v.1,hb⟩
    change InIncidenceRealization G S c.toNode ↔
      InJointPrunedRegion G S a c.toNode ∨ InJointPrunedRegion G S b c.toNode
    rw [branch_incidence_realization_iff,cn_branch_realization_iff G hB hCN]

end WaveTurbulence.Mole
