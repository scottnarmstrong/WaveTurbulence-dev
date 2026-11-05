/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineStemStarts
public import WaveTurbulence.Foundations.Molecule.VineEmptySlots
import Mathlib.Tactic

/-! # Arbitrary-rung type-II vines have no large inner block avoiding joints -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A connected block larger than a double bond cannot avoid both joints
inside a type-II vine. All its old and fresh rung pairs are forced absent. -/
theorem typeII_no_large_inner (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : VineRealization M .II S a b) (hS : M.IsBlock S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A)
    (hAS : A ⊆ S) (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A) : False := by
  have hlen : R.k.length=1 := R.length_eq
  obtain ⟨kr,hks⟩ := List.length_eq_one_iff.mp hlen
  have hleft := stemStarts_absent M hM R hS hA hC hcard ha hb ⟨0,0,2,3⟩ (by exact List.mem_cons_self)
  have hred := block_empty_slot_from_start M hM R hA hC hcard [] []
    ((2,1),(3,1)) kr (by rw [hks]; rfl) hleft
  have hred' : ∀ v ∈ S,4 ≤ R.f v → R.f v<4+2*kr → v ∉ A := by
    simpa only [List.foldl_nil,VineType.template] using hred
  have hv : x ∈ A := hA.2.1
  have hvS := hAS hv
  have hbound := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hvS)
  rw [hks,expand_atoms] at hbound
  norm_num [VineType.template] at hbound
  have hlo : 2 ≤ R.f x := by
    by_contra hh
    have hlt : R.f x<2 := by omega
    rcases (realization_index_lt_two_iff R hS hvS).mp hlt with he | he
    · exact ha (he ▸ hv)
    · exact hb (he ▸ hv)
  have hn2 : R.f x ≠ 2 := fun he => hleft x hvS (Or.inl he) hv
  have hn3 : R.f x ≠ 3 := fun he => hleft x hvS (Or.inr he) hv
  exact hred' x hvS (by omega) hbound hv

end WaveTurbulence.Vine
