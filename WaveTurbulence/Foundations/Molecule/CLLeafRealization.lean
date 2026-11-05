/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.PrunedChildExtension
public import WaveTurbulence.Foundations.Molecule.LeafSlots
import Mathlib.Tactic

/-! # Exact CL realization including its completely paired leaves
TARGET `block_clcn` (CL)(iii). Membership is proved for the actual garden
nodes and LP involution; no pairing closure is assumed.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem pruned_nonroot_slot_internal {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) {v : GNode G.tree}
    (hv : InCLPrunedRegion G S a b v) (hne : v ≠ a.toNode) (hn : v.1.2 ≠ []) :
    (v.1.2.getLast hn).succ ∈ internalPositions G S (GNode.parent v hn) := by
  classical
  let p := GNode.parent v hn
  have hp : p ∈ S := joint_pruned_branch_mem G hB p (pruned_parent G hv hne hn)
  by_contra hm
  have hj : p ∈ ({a,b} : Finset (GBranch G.tree)) := by
    by_contra hj
    have hpa : p ≠ a := fun h => hj (by simp [h])
    have hpb : p ≠ b := fun h => hj (by simp [h])
    have hf := full_internalPositions G (hB.2.2.2.2.2.2.2.2.1 p hp hpa hpb)
    change (v.1.2.getLast hn).succ ∉ internalPositions G S p at hm
    rw [hf] at hm
    exact hm (mem_univ _)
  apply hv.2 p hj _ hm
  refine ⟨rfl,?_⟩
  change (v.1.2.dropLast++[v.1.2.getLast hn]) <+: v.1.2
  rw [List.dropLast_append_getLast]

theorem cl_leaf_realization_iff {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (l : GLeaf G.tree) :
    IsInternalLeaf G S l ↔ InCLPrunedRegion G S a b l.toNode := by
  constructor
  · intro hl
    obtain ⟨hm,hn,hpair,hg⟩ := hl
    have hp : GNode.parent l.toNode hn ∈ S := hg.1
    have hpr := (cl_branch_realization_iff G hB hCL _).mp hp
    have hi := (leaf_slot_internal_iff G S l hn).mpr ⟨hm,hn,hpair,hg⟩
    have he := parent_child_eq_node (tree := G.tree) l.toNode hn
    exact he ▸ cl_pruned_child_extension G hpr _ hi
  · intro hl
    have hne : l.toNode ≠ a.toNode := (branch_toNode_ne_leaf a l).symm
    have hn := pruned_node_nonroot G hl hne
    exact (leaf_slot_internal_iff G S l hn).mp (pruned_nonroot_slot_internal G hB hl hne hn)

/-- The actual complete node-set equality for the CL realization. -/
theorem cl_node_realization_iff {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (v : GNode G.tree) :
    InIncidenceRealization G S v ↔ InCLPrunedRegion G S a b v := by
  rcases (TTree.mem_nodes_iff _ _).mp v.2 with hl | hb
  · let l : GLeaf G.tree := ⟨v.1,hl⟩
    change InIncidenceRealization G S l.toNode ↔ InCLPrunedRegion G S a b l.toNode
    rw [leaf_incidence_realization_iff,cl_leaf_realization_iff G hB hCL]
  · let c : GBranch G.tree := ⟨v.1,hb⟩
    change InIncidenceRealization G S c.toNode ↔ InCLPrunedRegion G S a b c.toNode
    rw [branch_incidence_realization_iff,cl_branch_realization_iff G hB hCL]

/-- All leaves of the actual pruned CL realization are unmarked and paired
to leaves of the same realization. -/
theorem cl_realization_completely_paired {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b)
    (l : GLeaf G.tree) (hl : InCLPrunedRegion G S a b l.toNode) :
    G.mark l = none ∧ InCLPrunedRegion G S a b (G.pair l).toNode := by
  have hi := (cl_leaf_realization_iff G hB hCL l).mpr hl
  exact ⟨internal_leaf_unmarked G hi,(cl_leaf_realization_iff G hB hCL _).mp
    ((internal_leaf_pair_iff G S l).mpr hi)⟩

end WaveTurbulence.Mole
