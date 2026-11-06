/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
import Mathlib.Tactic

/-! # Transport of the actual source hypotheses under joint reordering -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- Equality of two unordered joint pairs has exactly the two possible orders. -/
theorem finset_pair_eq_pair_iff {a b c d : V} :
    ({a,b}:Finset V) = {c,d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [← Finset.coe_inj]
  simpa only [Finset.coe_pair] using (Set.pair_eq_pair_iff (x := a) (y := b) (z := c) (w := d))

omit [DecidableEq D] in
/-- Actual block predicates transport along equality of their joint sets. -/
theorem block_transport_joints {S : Finset V} {a b c d : V}
    (he : ({a,b}:Finset V) = {c,d}) (hB : M.IsBlock S c d) : M.IsBlock S a b := by
  rcases finset_pair_eq_pair_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hB
  · exact block_swap_joints M hB

/-- Choose any specified joint as the first joint while retaining all
source connected-interior and vertex-deletion hypotheses. -/
theorem reorder_joint_first {S : Finset V} {a b x : V} (R : BlockRealization M S a b)
    (hx : x ∈ ({a,b}:Finset V)) (hd : InteriorDeletionProperty M S a b)
    (hi : ∀ u ∈ S \ {a,b}, ∀ v ∈ S \ {a,b}, (induced M (S \ {a,b})).SameComponent u v) :
    ∃ y : V, Nonempty (BlockRealization M S x y) ∧ ({a,b}:Finset V) = {x,y} ∧
      InteriorDeletionProperty M S x y ∧
      ∀ u ∈ S \ {x,y}, ∀ v ∈ S \ {x,y}, (induced M (S \ {x,y})).SameComponent u v := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b,⟨R⟩,rfl,hd,hi⟩
  · refine ⟨a,⟨R.swap⟩,Finset.pair_comm _ _,interiorDeletionProperty_swap M hd,?_⟩
    have he := congrArg (fun T : Finset V => S \ T) (Finset.pair_comm a x)
    exact he ▸ hi

/-- The corresponding source-hypothesis transport when a common joint
is specified as the second joint. -/
theorem reorder_joint_second {S : Finset V} {a b x : V} (R : BlockRealization M S a b)
    (hx : x ∈ ({a,b}:Finset V)) (hd : InteriorDeletionProperty M S a b)
    (hi : ∀ u ∈ S \ {a,b}, ∀ v ∈ S \ {a,b}, (induced M (S \ {a,b})).SameComponent u v) :
    ∃ y : V, Nonempty (BlockRealization M S y x) ∧ ({a,b}:Finset V) = {y,x} ∧
      InteriorDeletionProperty M S y x ∧
      ∀ u ∈ S \ {y,x}, ∀ v ∈ S \ {y,x}, (induced M (S \ {y,x})).SameComponent u v := by
  obtain ⟨y,⟨R'⟩,he,hd',hi'⟩ := reorder_joint_first M R hx hd hi
  refine ⟨y,⟨R'.swap⟩,he.trans (Finset.pair_comm _ _),interiorDeletionProperty_swap M hd',?_⟩
  have hs := congrArg (fun T : Finset V => S \ T) (Finset.pair_comm x y)
  exact hs ▸ hi'

end WaveTurbulence.Mole
