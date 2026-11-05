/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.PrunedParents
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
import Mathlib.Tactic

/-! # CN branching nodes are the union of two once-pruned subtrees
TARGET `block_clcn` (CN)(ii)–(iii), branching-node part.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- One joint's subtree with its missing internal child subtrees removed. -/
@[expose] def InJointPrunedRegion (S : Finset (GBranch G.tree)) (a : GBranch G.tree)
    (v : GNode G.tree) : Prop :=
  a.toNode.IsDesc v ∧ ∀ i : Fin 3,
    i.succ ∉ internalPositions G S a → ¬ (a.child i).IsDesc v

theorem cn_other_joint_not_pruned {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hb : ¬ InternalParent G S b) :
    ¬ InJointPrunedRegion G S a b.toNode := by
  intro hr
  obtain ⟨i,hi,hd⟩ := cn_joint_separation G hB hb hr.1
  exact hr.2 i hi hd

theorem joint_pruned_branch_mem_of_other_parent_outside
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hb : ¬ InternalParent G S b)
    (v : GBranch G.tree) (hv : InJointPrunedRegion G S a v.toNode) : v ∈ S := by
  classical
  by_cases he : v = a
  · exact he ▸ hB.2.1
  have hn : v.1.2 ≠ [] := by
    intro hn
    have ha : a.1.2 = [] := List.prefix_nil.mp (hn ▸ hv.1.2)
    exact he (Subtype.ext (Prod.ext hv.1.1.symm (hn.trans ha.symm)))
  let p := GNode.parent v.toNode hn
  have hpregion : InJointPrunedRegion G S a p.toNode := by
    refine ⟨⟨hv.1.1,proper_prefix_dropLast hv.1.2 ?_⟩,?_⟩
    · intro hpath
      exact he (Subtype.ext (Prod.ext hv.1.1.symm hpath.symm))
    · intro i hi hd
      exact hv.2 i hi ⟨hd.1,hd.2.trans (List.dropLast_prefix _)⟩
  have hp : p ∈ S := joint_pruned_branch_mem_of_other_parent_outside hB hb p hpregion
  apply (parent_child_slot_internal_iff G S v hn hp).mp
  by_contra hm
  by_cases hpa : p = a
  · have hd : (p.child (v.1.2.getLast hn)).IsDesc v.toNode := by
      refine ⟨rfl,?_⟩
      change (v.1.2.dropLast++[v.1.2.getLast hn]) <+: v.1.2
      rw [List.dropLast_append_getLast]
    exact hv.2 _ (hpa ▸ hm) (hpa ▸ hd)
  have hpb : p ≠ b := by
    intro heq
    exact cn_other_joint_not_pruned G hB hb (heq ▸ hpregion)
  have hd := hB.2.2.2.2.2.2.2.2.1 p hp hpa hpb
  have hf := full_internalPositions G hd
  change (v.1.2.getLast hn).succ ∉ internalPositions G S p at hm
  rw [hf] at hm
  exact hm (mem_univ _)
termination_by v.1.2.length
decreasing_by
  dsimp only [p,GNode.parent,GBranch.toNode]
  rw [List.length_dropLast]
  have hpos := List.length_pos_of_ne_nil hn
  omega

theorem selected_branch_below_pruned_joint {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (v : GBranch G.tree) (hv : v ∈ S) :
    InJointPrunedRegion G S a v.toNode ∨ InJointPrunedRegion G S b v.toNode := by
  obtain ⟨r,hr,hd,hinterval⟩ := exists_region_root_interval G v hv
  have hc : InJointPrunedRegion G S r v.toNode := by
    refine ⟨hd,?_⟩
    intro i hi hchild
    have hbranch : (r.child i).1.2 ∈ (G.tree (r.child i).1.1).branching :=
      branching_of_prefix_branching _ (hchild.1.symm ▸ v.2) hchild.2
    let c : GBranch G.tree := ⟨(r.child i).1,hbranch⟩
    have hrc : r.toNode.IsDesc c.toNode := ⟨rfl,List.prefix_append _ _⟩
    have hc := hinterval c hrc hchild
    exact hi ((branching_child_slot_iff G hr.1 i hbranch).mpr hc)
  rcases block_region_roots_are_joints G hB hr with he | he
  · exact Or.inl (he ▸ hc)
  · exact Or.inr (he ▸ hc)

/-- Exact CN branch realization, including the case of nested joints. -/
theorem cn_branch_realization_iff {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCN : CNParentPattern G S a b) (v : GBranch G.tree) :
    v ∈ S ↔ InJointPrunedRegion G S a v.toNode ∨ InJointPrunedRegion G S b v.toNode := by
  constructor
  · exact selected_branch_below_pruned_joint G hB v
  · rintro (ha | hb)
    · exact joint_pruned_branch_mem_of_other_parent_outside G hB hCN.2 v ha
    · exact joint_pruned_branch_mem_of_other_parent_outside G
        (block_swap_joints G.molecule hB) hCN.1 v hb

end WaveTurbulence.Mole
