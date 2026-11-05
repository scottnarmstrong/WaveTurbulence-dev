/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ExcludedChildren
import Mathlib.Tactic

/-! # CL branching nodes are exactly the pruned descendant set
TARGET `block_clcn` (CL)(iii), branching-node part. The excluded child
slots are the actual missing internal incidences at the two joints.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem full_internalPositions {S : Finset (GBranch G.tree)} {v : GBranch G.tree}
    (hd : G.molecule.degIn S v = 4) : internalPositions G S v = univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [card_internalPositions,hd]
  decide

/-- Descendants of the upper joint after removing precisely the missing
child subtrees at the two joints. -/
@[expose] def InCLPrunedRegion (S : Finset (GBranch G.tree)) (a b : GBranch G.tree)
    (v : GNode G.tree) : Prop :=
  a.toNode.IsDesc v ∧ ∀ j ∈ ({a,b} : Finset (GBranch G.tree)), ∀ i : Fin 3,
    i.succ ∉ internalPositions G S j → ¬ (j.child i).IsDesc v

theorem joint_pruned_branch_mem {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b)
    (v : GBranch G.tree) (hv : InCLPrunedRegion G S a b v.toNode) : v ∈ S := by
  classical
  by_cases he : v = a
  · exact he ▸ hB.2.1
  have hn : v.1.2 ≠ [] := by
    intro hn
    have ha : a.1.2 = [] := List.prefix_nil.mp (hn ▸ hv.1.2)
    exact he (Subtype.ext (Prod.ext hv.1.1.symm (hn.trans ha.symm)))
  let p := GNode.parent v.toNode hn
  have hap : a.toNode.IsDesc p.toNode := by
    refine ⟨hv.1.1,proper_prefix_dropLast hv.1.2 ?_⟩
    intro hpath
    exact he (Subtype.ext (Prod.ext hv.1.1.symm hpath.symm))
  have hpv : p.toNode.IsDesc v.toNode := ⟨rfl,List.dropLast_prefix _⟩
  have hpregion : InCLPrunedRegion G S a b p.toNode := by
    refine ⟨hap,?_⟩
    intro j hj i hi hd
    exact hv.2 j hj i hi ⟨hd.1,hd.2.trans hpv.2⟩
  have hp : p ∈ S := joint_pruned_branch_mem hB p hpregion
  apply (parent_child_slot_internal_iff G S v hn hp).mp
  by_contra hm
  have hj : p ∈ ({a,b} : Finset (GBranch G.tree)) := by
    by_contra hj
    have hpa : p ≠ a := fun h => hj (by simp [h])
    have hpb : p ≠ b := fun h => hj (by simp [h])
    have hd := hB.2.2.2.2.2.2.2.2.1 p hp hpa hpb
    have hf := full_internalPositions G hd
    change (v.1.2.getLast hn).succ ∉ internalPositions G S p at hm
    rw [hf] at hm
    exact hm (mem_univ _)
  apply hv.2 p hj (v.1.2.getLast hn) hm
  refine ⟨rfl,?_⟩
  change (v.1.2.dropLast ++ [v.1.2.getLast hn]) <+: v.1.2
  rw [List.dropLast_append_getLast]
termination_by v.1.2.length
decreasing_by
  dsimp only [p,GNode.parent,GBranch.toNode]
  rw [List.length_dropLast]
  have hpos := List.length_pos_of_ne_nil hn
  omega

/-- Exact equality of the actual selected branching atoms and the CL
descendant-set realization, with no assumed realization equivalence. -/
theorem cl_branch_realization_iff {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (v : GBranch G.tree) :
    v ∈ S ↔ InCLPrunedRegion G S a b v.toNode := by
  constructor
  · intro hv
    refine ⟨block_one_root_descendants G hB hCL.1 hCL.2 hv,?_⟩
    intro j hj i hi
    have hjS : j ∈ S := by
      simp only [mem_insert,mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact hB.2.1
      · exact hB.2.2.1
    exact cl_excluded_child_no_descendant G hB hCL hjS hv i hi
  · exact joint_pruned_branch_mem G hB v

end WaveTurbulence.Mole
