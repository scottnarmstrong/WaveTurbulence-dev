/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenMoleculeAxioms
public import WaveTurbulence.Foundations.Molecule.GardenPositionReconstruction
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
import Mathlib.Tactic

/-! # Parent flow inside a garden block

DH23 Proposition 4.12, parent-following step, used by TARGET `block_clcn`.
The parent relation here is the actual tree parent, not an auxiliary graph.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- The actual parent incidence is internal to the selected atom set. -/
@[expose] def InternalParent (S : Finset (GBranch G.tree)) (v : GBranch G.tree) : Prop :=
  ∃ h : v.1.2 ≠ [], GNode.parent v.toNode h ∈ S

theorem full_internal_has_parent {S : Finset (GBranch G.tree)} {v : GBranch G.tree}
    (hd : G.molecule.degIn S v = 4) : InternalParent G S v := by
  have hn : v.1.2 ≠ [] := by
    intro hr
    have h1 := degIn_le_deg G.molecule S v
    have h2 := root_degree_le_three G v hr
    omega
  refine ⟨hn,?_⟩
  exact full_degree_no_exit G.molecule (garden_isMolecule G) (mem_univ v) hd
    (x := .inl (⟨v,hn⟩,false)) rfl

/-- An interior atom cannot terminate the parent flow. -/
theorem block_interior_has_parent {S : Finset (GBranch G.tree)} {a b v : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hv : v ∈ S) (ha : v ≠ a) (hb : v ≠ b) :
    InternalParent G S v :=
  full_internal_has_parent G (hB.2.2.2.2.2.2.2.2.1 v hv ha hb)

/-- Every atom reaches a joint by repeatedly taking actual internal parents.
The path-length bound also records that no cycle can be hidden in this flow. -/
theorem block_parent_reaches_joint {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (v : GBranch G.tree) (hv : v ∈ S) :
    ∃ j ∈ ({a,b} : Finset (GBranch G.tree)), j.1.1 = v.1.1 ∧
      j.1.2 <+: v.1.2 := by
  by_cases ha : v = a
  · subst v
    exact ⟨a,by simp,rfl,List.prefix_refl _⟩
  by_cases hb : v = b
  · subst v
    exact ⟨b,by simp,rfl,List.prefix_refl _⟩
  obtain ⟨hn,hp⟩ := block_interior_has_parent G hB hv ha hb
  let p := GNode.parent v.toNode hn
  obtain ⟨j,hj,hi,he⟩ := block_parent_reaches_joint hB p hp
  refine ⟨j,hj,hi,he.trans ?_⟩
  exact List.dropLast_prefix _
termination_by v.1.2.length
decreasing_by
  dsimp only [p,GNode.parent,GBranch.toNode]
  rw [List.length_dropLast]
  have hpos := List.length_pos_of_ne_nil hn
  omega

/-- A joint with an internal parent is strictly below the other joint. -/
theorem internal_parent_joint_length {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (ha : InternalParent G S a) :
    b.1.2.length < a.1.2.length := by
  obtain ⟨hn,hp⟩ := ha
  obtain ⟨j,hj,_hi,he⟩ := block_parent_reaches_joint G hB (GNode.parent a.toNode hn) hp
  have hle := List.IsPrefix.length_le he
  change j.1.2.length ≤ a.1.2.dropLast.length at hle
  rw [List.length_dropLast] at hle
  have hpos := List.length_pos_of_ne_nil hn
  simp only [mem_insert,mem_singleton] at hj
  rcases hj with rfl | rfl
  · omega
  · omega

/-- DH23 Proposition 4.12: both joints cannot have their parent inside.
Thus the two genuine possibilities are one internal parent (CL), or none (CN). -/
theorem block_parent_dichotomy {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) :
    (InternalParent G S a ∧ ¬ InternalParent G S b) ∨
    (¬ InternalParent G S a ∧ InternalParent G S b) ∨
    (¬ InternalParent G S a ∧ ¬ InternalParent G S b) := by
  classical
  have hno : ¬ (InternalParent G S a ∧ InternalParent G S b) := by
    rintro ⟨ha,hb⟩
    have h1 := internal_parent_joint_length G hB ha
    have hswap : G.molecule.IsBlock S b a := block_swap_joints G.molecule hB
    have h2 := internal_parent_joint_length G hswap hb
    omega
  tauto

end WaveTurbulence.Mole
