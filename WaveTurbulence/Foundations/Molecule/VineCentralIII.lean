/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineStemStarts
public import WaveTurbulence.Foundations.Molecule.VineEmptySlots
import Mathlib.Tactic

/-! # Arbitrary-rung type-III stem exclusion leaves only its central group -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A connected block larger than a double bond and avoiding the outer
joints of a type-III vine can use only the central labels 4,5,6. Thus it
has at most three atoms, for completely arbitrary rung counts. -/
theorem typeIII_inner_card_le_three (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : VineRealization M .III S a b) (hS : M.IsBlock S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A)
    (hAS : A ⊆ S) (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A) : A.card ≤ 3 := by
  have hlen : R.k.length=2 := R.length_eq
  obtain ⟨kr,kg,hks⟩ := List.length_eq_two.mp hlen
  have hleft := stemStarts_absent M hM R hS hA hC hcard ha hb ⟨0,0,2,3⟩ (by exact List.mem_cons_self)
  have hright := stemStarts_absent M hM R hS hA hC hcard ha hb ⟨1,1,7,8⟩ (by exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hred := block_empty_slot_from_start M hM R hA hC hcard [] [(((4,7),(6,8)),kg)]
    ((2,4),(3,5)) kr (by rw [hks]; rfl) hleft
  have hgreen := block_empty_slot_from_end M hM R hA hC hcard [(((2,4),(3,5)),kr)] []
    ((4,7),(6,8)) kg (by rw [hks]; rfl) hright
  have hred' : ∀ v ∈ S,9 ≤ R.f v → R.f v<9+2*kr → v ∉ A := by
    simpa only [List.foldl_nil,VineType.template] using hred
  have hgreen' : ∀ v ∈ S,9+2*kr ≤ R.f v → R.f v<9+2*kr+2*kg → v ∉ A := by
    simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hgreen
  have himage : A.image R.f ⊆ ({4,5,6} : Finset ℕ) := by
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
    have hn2 : R.f v ≠ 2 := fun he => hleft v hvS (Or.inl he) hv
    have hn3 : R.f v ≠ 3 := fun he => hleft v hvS (Or.inr he) hv
    have hn7 : R.f v ≠ 7 := fun he => hright v hvS (Or.inl he) hv
    have hn8 : R.f v ≠ 8 := fun he => hright v hvS (Or.inr he) hv
    have hnred : ¬(9 ≤ R.f v ∧ R.f v<9+2*kr) := fun h => hred' v hvS h.1 h.2 hv
    have hngreen : ¬(9+2*kr ≤ R.f v ∧ R.f v<9+2*kr+2*kg) := fun h => hgreen' v hvS h.1 h.2 hv
    simp only [mem_insert,mem_singleton]
    omega
  have hc := card_le_card himage
  rw [card_image_of_injOn (fun _ hx _ hy he => R.injOn (hAS hx) (hAS hy) he)] at hc
  exact hc

end WaveTurbulence.Vine
