/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinkDegrees
import Mathlib.Tactic

/-! # Actual selected neighbours of a four-atom ladder link -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The selected double partner lies in the same link. -/
theorem AppbLink.partner_mem {M : Molecule V D} (hM : M.IsMolecule) {S : Finset V}
    (hS : AppbLink M S) {a b : V} (ha : a ∈ S) (hab : a ≠ b) (hdouble : M.bondsBetween a b = 2) :
    b ∈ S := by
  obtain ⟨u,v,hL,rfl⟩ := hS
  exact Degen.sourceLadder_partner_mem M (fun _ hx => deg_le_four M hM hx) hL ha hab hdouble

/-- Each link atom has a distinct selected single-rail neighbour inside
the link, with actual old multiplicity one. -/
theorem AppbLink.single_neighbor {M : Molecule V D} {S : Finset V}
    (hS : AppbLink M S) {a : V} (ha : a ∈ S) :
    ∃ b ∈ S,a ≠ b ∧ M.bondsBetween a b = 1 := by
  obtain ⟨u,v,hL,rfl⟩ := hS
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    obtain ⟨k,hkj,hrail⟩ := Degen.sourceLadder_u_single_neighbor M hL j
    obtain ⟨hu,hv,hcross⟩ := Sum.elim_injective.mp hL.2.1
    refine ⟨u k,mem_union_left _ (mem_image.mpr ⟨k,mem_univ _,rfl⟩),?_,hrail⟩
    exact fun he => hkj (hu he).symm
  · obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    obtain ⟨k,hkj,hrail⟩ := Degen.sourceLadder_u_single_neighbor M (Degen.sourceLadder_swap M hL) j
    obtain ⟨hu,hv,hcross⟩ := Sum.elim_injective.mp hL.2.1
    refine ⟨v k,mem_union_right _ (mem_image.mpr ⟨k,mem_univ _,rfl⟩),?_,hrail⟩
    exact fun he => hkj (hv he).symm

end WaveTurbulence.Mole
