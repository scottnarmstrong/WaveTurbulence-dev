/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineStemStarts
public import WaveTurbulence.Foundations.Molecule.VineEmptySlots
import Mathlib.Tactic

/-! # Type-VII ordinary blocks are confined to the central side ladder -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The red and green stems of type VII are absent from every connected
inner block larger than a double bond avoiding the outer joints. The only
remaining labels are the five-atom side core and its cyan allocation. -/
theorem typeVII_inner_side_region (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b) (hS : M.IsBlock S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A)
    (hAS : A ⊆ S) (hcard : 2<A.card) (ha : a ∉ A) (hb : b ∉ A) :
    ∃ kr kc kg,R.k=[kr,kc,kg] ∧ ∀ v ∈ A,
      R.f v=4 ∨ R.f v=5 ∨ R.f v=6 ∨ R.f v=7 ∨ R.f v=8 ∨
        (11+2*kr ≤ R.f v ∧ R.f v<11+2*kr+2*kc) := by
  have hlen : R.k.length=3 := R.length_eq
  obtain ⟨kr,kc,kg,hks⟩ := List.length_eq_three.mp hlen
  have hleft := stemStarts_absent M hM R hS hA hC hcard ha hb ⟨0,0,2,3⟩ (by exact List.mem_cons_self)
  have hright := stemStarts_absent M hM R hS hA hC hcard ha hb ⟨1,1,9,10⟩
    (by exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hred := block_empty_slot_from_start M hM R hA hC hcard []
    [(((5,7),(6,8)),kc),(((7,9),(8,10)),kg)] ((2,7),(3,8)) kr (by rw [hks]; rfl) hleft
  have hgreen := block_empty_slot_from_end M hM R hA hC hcard
    [(((2,7),(3,8)),kr),(((5,7),(6,8)),kc)] [] ((7,9),(8,10)) kg (by rw [hks]; rfl) hright
  have hred' : ∀ v ∈ S,11 ≤ R.f v → R.f v<11+2*kr → v ∉ A := by
    simpa only [List.foldl_nil,VineType.template] using hred
  have hgreen' : ∀ v ∈ S,11+2*kr+2*kc ≤ R.f v → R.f v<11+2*kr+2*kc+2*kg → v ∉ A := by
    simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hgreen
  refine ⟨kr,kc,kg,hks,?_⟩
  intro v hv
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
  have hn9 : R.f v ≠ 9 := fun he => hright v hvS (Or.inl he) hv
  have hn10 : R.f v ≠ 10 := fun he => hright v hvS (Or.inr he) hv
  have hnred : ¬(11 ≤ R.f v ∧ R.f v<11+2*kr) := fun h => hred' v hvS h.1 h.2 hv
  have hngreen : ¬(11+2*kr+2*kc ≤ R.f v ∧ R.f v<11+2*kr+2*kc+2*kg) := fun h => hgreen' v hvS h.1 h.2 hv
  omega

end WaveTurbulence.Vine
