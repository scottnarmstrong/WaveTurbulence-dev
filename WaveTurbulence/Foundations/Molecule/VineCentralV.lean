/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineStemStarts
public import WaveTurbulence.Foundations.Molecule.VineSlotPropagation
import Mathlib.Tactic

/-! # Arbitrary-rung type-V exclusion leaves its side triple -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Avoiding the two outer joints forces the stem of a type-V vine absent;
a connected inner block larger than a double bond then has at most three
atoms, all in the side triple 6,7,8. -/
theorem typeV_inner_card_le_three (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : VineRealization M .V S a b) (hS : M.IsBlock S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A)
    (hAS : A ⊆ S) (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A) : A.card ≤ 3 := by
  have hlen : R.k.length=1 := R.length_eq
  obtain ⟨kr,hks⟩ := List.length_eq_one_iff.mp hlen
  have hfirst := stemStarts_absent M hM R hS hA hC hcard ha hb ⟨0,1,2,3⟩ (by exact List.mem_cons_self)
  have hnext := block_slot_double_end_absent_all M hM R hA hC hcard [] []
    ((2,4),(3,5)) kr (by rw [hks]; rfl) (by decide) (by decide) hfirst
  have hslot := block_empty_slot_from_start M hM R hA hC hcard [] []
    ((2,4),(3,5)) kr (by rw [hks]; rfl) hfirst
  have hslot' : ∀ v ∈ S,9 ≤ R.f v → R.f v<9+2*kr → v ∉ A := by
    simpa only [List.foldl_nil,VineType.template] using hslot
  have himage : A.image R.f ⊆ ({6,7,8} : Finset ℕ) := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    have hvS := hAS hv
    have hbound := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hvS)
    rw [hks,expand_atoms] at hbound
    norm_num [VineType.template] at hbound
    have hlo : 2 ≤ R.f v := by
      by_contra hh
      have hlt : R.f v<2 := by omega
      rcases (realization_index_lt_two_iff R hS hvS).mp hlt with he | he
      · exact ha (he ▸ hv)
      · exact hb (he ▸ hv)
    have hn2 : R.f v ≠ 2 := fun he => hfirst v hvS (Or.inl he) hv
    have hn3 : R.f v ≠ 3 := fun he => hfirst v hvS (Or.inr he) hv
    have hn4 : R.f v ≠ 4 := fun he => hnext v hvS (Or.inl he) hv
    have hn5 : R.f v ≠ 5 := fun he => hnext v hvS (Or.inr he) hv
    have hnslot : ¬(9 ≤ R.f v ∧ R.f v<9+2*kr) := fun h => hslot' v hvS h.1 h.2 hv
    simp only [mem_insert,mem_singleton]
    omega
  have hc := card_le_card himage
  rw [card_image_of_injOn (fun _ hx _ hy he => R.injOn (hAS hx) (hAS hy) he)] at hc
  exact hc

end WaveTurbulence.Vine
