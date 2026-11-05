/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegionIncidences
import Mathlib.Tactic

/-! # Parent components contain their full ancestor intervals
TARGET `block_clcn`: this prevents a CL realization from leaving and
then re-entering an excluded child subtree.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem proper_prefix_dropLast {α : Type*} {p q : List α} (hp : p <+: q) (hn : p ≠ q) :
    p <+: q.dropLast := by
  obtain ⟨s,rfl⟩ := hp
  have hs : s ≠ [] := by
    intro he
    simp only [he,List.append_nil,ne_self_iff_false] at hn
  rw [List.dropLast_append_of_ne_nil hs]
  exact ⟨s.dropLast,rfl⟩

/-- A region root can be chosen with every branching ancestor between it
and the selected node still inside the selected set. -/
theorem exists_region_root_interval {S : Finset (GBranch G.tree)}
    (v : GBranch G.tree) (hv : v ∈ S) :
    ∃ r, IsRegionRoot G S r ∧ r.toNode.IsDesc v.toNode ∧
      ∀ b : GBranch G.tree, r.toNode.IsDesc b.toNode → b.toNode.IsDesc v.toNode → b ∈ S := by
  classical
  by_cases hp : InternalParent G S v
  · obtain ⟨hn,hp⟩ := hp
    let p := GNode.parent v.toNode hn
    obtain ⟨r,hr,hd,hinterval⟩ := exists_region_root_interval p hp
    refine ⟨r,hr,⟨hd.1,hd.2.trans (List.dropLast_prefix _)⟩,?_⟩
    intro b hrb hbv
    by_cases hb : b = v
    · exact hb ▸ hv
    · apply hinterval b hrb
      refine ⟨hbv.1,proper_prefix_dropLast hbv.2 ?_⟩
      intro heq
      exact hb (Subtype.ext (Prod.ext hbv.1 heq))
  · refine ⟨v,⟨hv,hp⟩,⟨rfl,List.prefix_refl _⟩,?_⟩
    intro b hvb hbv
    have he : b = v := Subtype.ext (Prod.ext hbv.1 (hbv.2.eq_of_length_le hvb.2.length_le))
    exact he ▸ hv
termination_by v.1.2.length
decreasing_by
  dsimp only [p,GNode.parent,GBranch.toNode]
  rw [List.length_dropLast]
  have hpos := List.length_pos_of_ne_nil hn
  omega

/-- The CL branch set is closed under taking branching ancestors down to its upper joint. -/
theorem cl_branch_interval {S : Finset (GBranch G.tree)} {a b v z : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (hv : v ∈ S)
    (haz : a.toNode.IsDesc z.toNode) (hzv : z.toNode.IsDesc v.toNode) : z ∈ S := by
  obtain ⟨r,hr,_hd,hinterval⟩ := exists_region_root_interval G v hv
  have he := (block_one_region_root G hB hCL.1 hCL.2 r).mp hr
  subst r
  exact hinterval z haz hzv

end WaveTurbulence.Mole
