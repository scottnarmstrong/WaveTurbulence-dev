/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
/-! Reversal of vine chains and the union of two ordinary objects at one joint. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceVine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem isVine_swap {X : VineType} {S : Finset V} {a b : V} (h : M.IsVine X S a b) :
    M.IsVine X S b a := by
  obtain ⟨hB, k, hk, f, hf, hi, hj, he⟩ := h
  exact ⟨Mole.block_swap_joints M hB, k, hk, f, hf, hi, by rw [Finset.pair_comm]; exact hj, he⟩

theorem isSomeVine_swap {S : Finset V} {a b : V} (h : IsSomeVine M S a b) :
    IsSomeVine M S b a := by
  obtain ⟨X, hX⟩ := h
  exact ⟨X, isVine_swap hX⟩

theorem chain_swap {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) :
    Chain M S b a n := by
  induction h with
  | single h => exact Chain.single (isSomeVine_swap h)
  | @append S T a b c n hS hT hi hne ih =>
    have h1 : Chain M T c b 1 := Chain.single (isSomeVine_swap hT)
    have h2 := chain_append_chain h1 ih (by rw [Finset.inter_comm]; exact hi)
    rw [Finset.union_comm] at h2
    rwa [Nat.add_comm] at h2

/-- Two ordinary chain objects meeting exactly at the joint `c`. -/
theorem chain_union_of_one_joint {S T : Finset V} {a b c : V} {n m : ℕ}
    (hS : Chain M S a c n) (hT : Chain M T c b m) (hST : S ∩ T = {c}) :
    Chain M (S ∪ T) a b (n + m) := chain_append_chain hS hT hST

end WaveTurbulence.LGSpine.SourceVine
