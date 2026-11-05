/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegionIntervals
import Mathlib.Tactic

/-! # A CL region never re-enters an excluded child subtree
TARGET `block_clcn` (CL)(ii) and the descendant-set realization.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset

theorem branching_of_prefix_branching (t : TTree) {p q : Path}
    (hq : q ∈ t.branching) (hp : p <+: q) : p ∈ t.branching := by
  obtain ⟨s,rfl⟩ := hp
  cases s with
  | nil => simpa only [List.append_nil] using hq
  | cons i tail =>
    apply TTree.branching_of_append_mem t (i := i)
    apply TTree.mem_nodes_of_prefix t (TTree.branching_subset_nodes t hq)
    exact ⟨tail,by simp only [List.append_assoc,List.singleton_append]⟩

variable {w : ℕ} (G : Garden w)

theorem branching_child_slot_iff {S : Finset (GBranch G.tree)} {v : GBranch G.tree}
    (hv : v ∈ S) (i : Fin 3) (hb : (v.child i).1.2 ∈ (G.tree (v.child i).1.1).branching) :
    i.succ ∈ internalPositions G S v ↔ (⟨(v.child i).1,hb⟩ : GBranch G.tree) ∈ S := by
  let c : GBranch G.tree := ⟨(v.child i).1,hb⟩
  have hn : c.1.2 ≠ [] := child_nonroot G v i
  have hp : GNode.parent c.toNode hn = v := by
    apply Subtype.ext
    simp only [c,GBranch.child,GBranch.toNode,GNode.parent,List.dropLast_append_cons,
      List.dropLast_singleton,List.append_nil]
  have hlast : c.1.2.getLast hn = i := List.getLast_append_singleton _
  have h := parent_child_slot_internal_iff G S c hn (hp.symm ▸ hv)
  rw [hp,hlast] at h
  exact h

/-- No selected branching node lies below any excluded child of a CL atom. -/
theorem cl_excluded_child_no_descendant {S : Finset (GBranch G.tree)} {a b z v : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b)
    (hz : z ∈ S) (hv : v ∈ S) (i : Fin 3)
    (hi : i.succ ∉ internalPositions G S z) : ¬ (z.child i).IsDesc v.toNode := by
  intro hd
  have hbranch : (z.child i).1.2 ∈ (G.tree (z.child i).1.1).branching := by
    apply branching_of_prefix_branching _ (q := v.1.2)
    · exact hd.1.symm ▸ v.2
    · exact hd.2
  let c : GBranch G.tree := ⟨(z.child i).1,hbranch⟩
  have hzc : z.toNode.IsDesc c.toNode := ⟨rfl,List.prefix_append _ _⟩
  have haz := block_one_root_descendants G hB hCL.1 hCL.2 hz
  have hac : a.toNode.IsDesc c.toNode := ⟨haz.1,haz.2.trans hzc.2⟩
  have hc := cl_branch_interval G hB hCL hv hac hd
  exact hi ((branching_child_slot_iff G hz i hbranch).mpr hc)

end WaveTurbulence.Mole
