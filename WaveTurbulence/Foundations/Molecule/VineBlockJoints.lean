/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineNestedGaps
import Mathlib.Tactic

/-! # The joints of a block are determined by its induced degrees -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Any degree-two atom in a block is one of its two joints. -/
theorem block_degree_two_joint (M : Molecule V D) {S : Finset V} {a b v : V}
    (hB : M.IsBlock S a b) (hv : v ∈ S) (hd : M.degIn S v=2) : v=a ∨ v=b := by
  by_contra hh
  have hne : v ≠ a ∧ v ≠ b := not_or.mp hh
  have h4 := hB.2.2.2.2.2.2.2.2.1 v hv hne.1 hne.2
  omega

/-- The unordered pair of block joints is unique for a fixed atom set. -/
theorem block_joints_unique (M : Molecule V D) {S : Finset V} {a b c d : V}
    (hB : M.IsBlock S a b) (hC : M.IsBlock S c d) :
    ({a,b} : Finset V)={c,d} := by
  have hab := Mole.block_joint_degrees M hB
  have hcd := Mole.block_joint_degrees M hC
  apply subset_antisymm
  · intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · simpa only [mem_insert,mem_singleton] using block_degree_two_joint M hC hB.2.1 hab.1
    · have he := mem_singleton.mp hv
      subst v
      simpa only [mem_insert,mem_singleton] using block_degree_two_joint M hC hB.2.2.1 hab.2
  · intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · simpa only [mem_insert,mem_singleton] using block_degree_two_joint M hB hC.2.1 hcd.1
    · have he := mem_singleton.mp hv
      subst v
      simpa only [mem_insert,mem_singleton] using block_degree_two_joint M hB hC.2.2.1 hcd.2

end WaveTurbulence.Vine
