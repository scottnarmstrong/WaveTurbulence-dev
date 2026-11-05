/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineActualPartition
import Mathlib.Tactic

/-! # A second branch meets a vine exactly at its two joints -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- If another branch intersects a source vine only at its joints, its
atoms inside the vine are exactly the two labels below two. -/
theorem VineRealization.mem_other_branch_iff {M : Molecule V D} {X : VineType}
    {B : Finset V} {a b : V} (R : VineRealization M X B a b) (hB : M.IsBlock B a b)
    (A : Finset V) (hi : A ∩ B={a,b}) {v : V} (hv : v ∈ B) : v ∈ A ↔ R.f v<2 := by
  rw [realization_index_lt_two_iff R hB hv]
  constructor
  · intro hvA
    have hh := mem_inter.mpr ⟨hvA,hv⟩
    rw [hi] at hh
    simpa only [mem_insert,mem_singleton] using hh
  · intro hj
    have hh : v ∈ ({a,b} : Finset V) := by simpa only [mem_insert,mem_singleton] using hj
    rw [← hi] at hh
    exact (mem_inter.mp hh).1

/-- Every atom of the retained branch survives deletion of the other
branch's nonjoint interior. -/
theorem other_branch_atoms_survive {A B : Finset V} {a b v : V}
    (hi : A ∩ B={a,b}) (hv : v ∈ B) : v ∉ A \ {a,b} := by
  intro hdel
  have hh := mem_inter.mpr ⟨(mem_sdiff.mp hdel).1,hv⟩
  rw [hi] at hh
  exact (mem_sdiff.mp hdel).2 hh

/-- Nonjoint atoms of the retained vine are outside the other branch. -/
theorem VineRealization.nonjoint_outside_other_branch {M : Molecule V D} {X : VineType}
    {B : Finset V} {a b : V} (R : VineRealization M X B a b) (hB : M.IsBlock B a b)
    (A : Finset V) (hi : A ∩ B={a,b}) {v : V} (hv : v ∈ B) (hlabel : 2 ≤ R.f v) : v ∉ A := by
  intro hvA
  have hh := (R.mem_other_branch_iff hB A hi hv).mp hvA
  omega

end WaveTurbulence.Vine
