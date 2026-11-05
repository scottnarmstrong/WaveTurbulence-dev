/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainConnected
import Mathlib.Tactic

/-! # The component barrier for nested blocks (TARGET subsetvc)

A block's interior atoms have all four incidences within that block. Its
membership is consequently constant along paths avoiding its two joints.
-/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- No path avoiding the joints can cross a block boundary. -/
theorem block_membership_constant (hM : M.IsMolecule) {S T : Finset V} {a b u v : V}
    (hS : M.IsBlock S a b)
    (hp : (Mole.induced M (T \ {a,b})).SameComponent u v) : u ∈ S ↔ v ∈ S := by
  apply Mole.induced_path_barrier M hM hS.1 ?_ hp
  intro x hx hxT
  have hnot := (mem_sdiff.mp hxT).2
  have hxa : x ≠ a := by intro h; exact hnot (by simp only [h,mem_insert,mem_singleton,true_or])
  have hxb : x ≠ b := by intro h; exact hnot (by simp only [h,mem_insert,mem_singleton,or_true])
  exact hS.2.2.2.2.2.2.2.2.1 x hx hxa hxb

/-- A nested block consists of its joints and entire components of the
outer graph punctured at those joints. -/
theorem block_component_subset (hM : M.IsMolecule) {S T : Finset V} {a b u : V}
    (hS : M.IsBlock S a b) (hu : u ∈ S) :
    ∀ v ∈ T \ {a,b}, (Mole.induced M (T \ {a,b})).SameComponent u v → v ∈ S := by
  intro v _hv hp
  exact (block_membership_constant M hM hS hp).mp hu

/-- When the punctured outer group is connected, a same-joint nested block
containing an interior atom must fill the outer group. -/
theorem nested_block_eq_of_punctured_connected (hM : M.IsMolecule)
    {S T : Finset V} {a b : V} (hS : M.IsBlock S a b) (hST : S ⊆ T)
    (hT : GroupConnected M (T \ {a,b})) (hint : (S \ {a,b}).Nonempty) : S=T := by
  apply subset_antisymm hST
  intro v hv
  by_cases hvj : v ∈ ({a,b} : Finset V)
  · rcases mem_insert.mp hvj with rfl | hvb
    · exact hS.2.1
    · have he : v=b := mem_singleton.mp hvb
      subst v
      exact hS.2.2.1
  · obtain ⟨u,hu⟩ := hint
    have huS := (mem_sdiff.mp hu).1
    have huT : u ∈ T \ {a,b} := mem_sdiff.mpr ⟨hST huS,(mem_sdiff.mp hu).2⟩
    have hvT : v ∈ T \ {a,b} := mem_sdiff.mpr ⟨hv,hvj⟩
    exact (block_membership_constant M hM hS (hT u huT v hvT)).mp huS

end WaveTurbulence.Vine
