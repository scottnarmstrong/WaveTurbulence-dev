/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CNLeafRealization
public import WaveTurbulence.Foundations.Molecule.JointChildSlots
import Mathlib.Tactic

/-! # Source descendant formulas from the actual joint slots
TARGET `block_clcn`: three excluded child subtrees for CL, and one
excluded child subtree at each joint for CN.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem cl_pruned_region_explicit {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {excluded kept : Fin 3}
    (ha : ∀ i : Fin 3, i.succ ∈ internalPositions G S a ↔ i ≠ excluded)
    (hb : ∀ i : Fin 3, i.succ ∈ internalPositions G S b ↔ i = kept)
    (v : GNode G.tree) :
    InCLPrunedRegion G S a b v ↔
      a.toNode.IsDesc v ∧ ¬ (a.child excluded).IsDesc v ∧
        ∀ i : Fin 3, i ≠ kept → ¬ (b.child i).IsDesc v := by
  constructor
  · intro hv
    refine ⟨hv.1,hv.2 a (by simp) excluded ?_,?_⟩
    · exact fun h => (ha excluded).mp h rfl
    · intro i hi
      exact hv.2 b (by simp) i (fun h => hi ((hb i).mp h))
  · rintro ⟨hd,haDesc,hbDesc⟩
    refine ⟨hd,?_⟩
    intro j hj i hi
    simp only [mem_insert,mem_singleton] at hj
    rcases hj with he | he
    · subst j
      have heq : i = excluded := by
        by_contra hn
        exact hi ((ha i).mpr hn)
      exact heq ▸ haDesc
    · subst j
      exact hbDesc i (fun he => hi ((hb i).mpr he))

theorem joint_pruned_region_explicit {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    {excluded : Fin 3}
    (ha : ∀ i : Fin 3, i.succ ∈ internalPositions G S a ↔ i ≠ excluded)
    (v : GNode G.tree) : InJointPrunedRegion G S a v ↔
      a.toNode.IsDesc v ∧ ¬ (a.child excluded).IsDesc v := by
  constructor
  · intro hv
    exact ⟨hv.1,hv.2 excluded (fun h => (ha excluded).mp h rfl)⟩
  · rintro ⟨hd,hnot⟩
    refine ⟨hd,?_⟩
    intro i hi
    have heq : i = excluded := by
      by_contra hn
      exact hi ((ha i).mpr hn)
    exact heq ▸ hnot

/-- TARGET `block_clcn` (CL): the actual complete realization, child signs,
strict ancestry and exclusion. The two removed children below are exactly
the children other than `kept`; they can be labelled by their opposite signs. -/
theorem cl_source_realization {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) :
    ∃ excluded kept : Fin 3,
      G.sign (a.child excluded) = G.sign a.toNode ∧
      G.sign (b.child kept) = G.sign b.toNode ∧
      a.toNode.IsDesc b.toNode ∧ ¬ (a.child excluded).IsDesc b.toNode ∧
      ∀ v : GNode G.tree, InIncidenceRealization G S v ↔
        a.toNode.IsDesc v ∧ ¬ (a.child excluded).IsDesc v ∧
          ∀ i : Fin 3, i ≠ kept → ¬ (b.child i).IsDesc v := by
  obtain ⟨i,j,hi,hj,ha,hb⟩ := cl_joint_child_slots G hB hCL
  have hd := (cl_parent_strict_descendant G hB hCL).1
  have havoid := cl_excluded_child_no_descendant G hB hCL hB.2.1 hB.2.2.1 i
    (fun h => (ha i).mp h rfl)
  refine ⟨i,j,hi,hj,hd,havoid,?_⟩
  intro v
  rw [cl_node_realization_iff G hB hCL,cl_pruned_region_explicit G ha hb]

/-- TARGET `block_clcn` (CN): the actual complete realization and the
source's joint-separation alternatives for both orders of the joints. -/
theorem cn_source_realization {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCN : CNParentPattern G S a b) :
    ∃ excludedA excludedB : Fin 3,
      G.sign (a.child excludedA) = G.sign a.toNode ∧
      G.sign (b.child excludedB) = G.sign b.toNode ∧
      (a.toNode.IsDesc b.toNode → (a.child excludedA).IsDesc b.toNode) ∧
      (b.toNode.IsDesc a.toNode → (b.child excludedB).IsDesc a.toNode) ∧
      ∀ v : GNode G.tree, InIncidenceRealization G S v ↔
        (a.toNode.IsDesc v ∧ ¬ (a.child excludedA).IsDesc v) ∨
        (b.toNode.IsDesc v ∧ ¬ (b.child excludedB).IsDesc v) := by
  obtain ⟨i,hi,ha⟩ := no_parent_joint_excluded_child G hB.2.1 hB.2.2.2.2.1
    hB.2.2.2.2.2.1 hCN.1
  obtain ⟨j,hj,hb⟩ := no_parent_joint_excluded_child G hB.2.2.1 hB.2.2.2.2.2.2.1
    hB.2.2.2.2.2.2.2.1 hCN.2
  refine ⟨i,j,outer_child_sign G a i hi,outer_child_sign G b j hj,?_,?_,?_⟩
  · intro hd
    obtain ⟨k,hk,hkd⟩ := cn_joint_separation G hB hCN.2 hd
    have heq : k = i := by
      by_contra hn
      exact hk ((ha k).mpr hn)
    exact heq ▸ hkd
  · intro hd
    obtain ⟨k,hk,hkd⟩ := cn_joint_separation G (block_swap_joints G.molecule hB) hCN.1 hd
    have heq : k = j := by
      by_contra hn
      exact hk ((hb k).mpr hn)
    exact heq ▸ hkd
  · intro v
    rw [cn_node_realization_iff G hB hCN,joint_pruned_region_explicit G ha,
      joint_pruned_region_explicit G hb]

end WaveTurbulence.Mole
