/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockSlots
import Mathlib.Tactic

/-! # Actual forest regions cut out by parent incidences
TARGET `block_clcn`, DH23 Proposition 4.12: the roots of the pruned
forest are precisely the joints whose parent is outside the block.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- Roots of the forest induced by a set of branching nodes. -/
@[expose] def IsRegionRoot (S : Finset (GBranch G.tree)) (v : GBranch G.tree) : Prop :=
  v ∈ S ∧ ¬ InternalParent G S v

/-- Every selected branching node lies below an actual region root. -/
theorem exists_region_root {S : Finset (GBranch G.tree)} (v : GBranch G.tree) (hv : v ∈ S) :
    ∃ r, IsRegionRoot G S r ∧ r.toNode.IsDesc v.toNode := by
  classical
  by_cases hp : InternalParent G S v
  · obtain ⟨hn,hp⟩ := hp
    let p := GNode.parent v.toNode hn
    obtain ⟨r,hr,hi,he⟩ := exists_region_root p hp
    exact ⟨r,hr,hi,he.trans (List.dropLast_prefix _)⟩
  · exact ⟨v,⟨hv,hp⟩,rfl,List.prefix_refl _⟩
termination_by v.1.2.length
decreasing_by
  dsimp only [p,GNode.parent,GBranch.toNode]
  rw [List.length_dropLast]
  have hpos := List.length_pos_of_ne_nil hn
  omega

theorem block_region_roots_are_joints {S : Finset (GBranch G.tree)} {a b r : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hr : IsRegionRoot G S r) : r = a ∨ r = b := by
  by_contra hn
  push_neg at hn
  exact hr.2 (block_interior_has_parent G hB hr.1 hn.1 hn.2)

/-- The precise root set of a CN region consists of both joints. -/
theorem block_two_region_roots {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (ha : ¬ InternalParent G S a)
    (hb : ¬ InternalParent G S b) (r : GBranch G.tree) :
    IsRegionRoot G S r ↔ r = a ∨ r = b := by
  constructor
  · exact block_region_roots_are_joints G hB
  · rintro (rfl | rfl)
    · exact ⟨hB.2.1,ha⟩
    · exact ⟨hB.2.2.1,hb⟩

/-- The precise root set of a CL region consists of its upper joint. -/
theorem block_one_region_root {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (ha : ¬ InternalParent G S a)
    (hb : InternalParent G S b) (r : GBranch G.tree) :
    IsRegionRoot G S r ↔ r = a := by
  constructor
  · intro hr
    rcases block_region_roots_are_joints G hB hr with h | h
    · exact h
    · subst r
      exact (hr.2 hb).elim
  · rintro rfl
    exact ⟨hB.2.1,ha⟩

/-- In the CL case every atom is below the upper joint in the actual tree. -/
theorem block_one_root_descendants {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (ha : ¬ InternalParent G S a)
    (hb : InternalParent G S b) {v : GBranch G.tree} (hv : v ∈ S) :
    a.toNode.IsDesc v.toNode := by
  obtain ⟨r,hr,hd⟩ := exists_region_root G v hv
  have he := (block_one_region_root G hB ha hb r).mp hr
  subst r
  exact hd

end WaveTurbulence.Mole
