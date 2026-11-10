/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBoundary
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
import Mathlib.Tactic

/-! # Boundary sizes of blocks and hyper-blocks (TARGET subsetvc) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- Outside incidences at one atom. -/
@[expose] def outsideAt (S : Finset V) (v : V) : Finset D :=
  (M.dartsAt v).filter fun x => ¬ M.InGroup S x

omit [DecidableEq D] in
/-- Internal and outside incidences partition the atom's total degree. -/
theorem outsideAt_card_add (S : Finset V) (v : V) :
    (outsideAt M S v).card+M.degIn S v=M.deg v := by
  have hh := card_filter_add_card_filter_not (s := M.dartsAt v) (M.InGroup S)
  simpa only [outsideAt,Molecule.degIn,Molecule.deg,Nat.add_comm] using hh

/-- Only the joints of a block-shaped group can have outside incidences. -/
theorem boundary_subset_joints (hM : M.IsMolecule) {S : Finset V} {a b : V}
    (hS : S ⊆ M.atoms)
    (hint : ∀ v ∈ S, v ≠ a → v ≠ b → M.degIn S v=4) :
    boundary M S ⊆ outsideAt M S a ∪ outsideAt M S b := by
  intro x hx
  have hx' := (mem_filter.mp hx).2
  by_cases ha : M.atom x=a
  · apply mem_union_left
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M a x).mpr ha,fun hg => hx'.2 hg.2⟩
  · by_cases hb : M.atom x=b
    · apply mem_union_right
      exact mem_filter.mpr ⟨(Mole.mem_dartsAt M b x).mpr hb,fun hg => hx'.2 hg.2⟩
    · exact False.elim (hx'.2 (Mole.full_degree_no_exit M hM (hS hx'.1)
        (hint _ hx'.1 ha hb) rfl))

/-- A hyper-block has at most two boundary bonds (one at each joint). -/
theorem hyperBlock_boundary_card_le_two (hM : M.IsMolecule) {S : Finset V} {a b : V}
    (hB : Mole.IsHyperBlock M S a b) : (boundary M S).card ≤ 2 := by
  obtain ⟨ha,hb,hint⟩ := Mole.hyperBlock_degrees M hB
  obtain ⟨e,_he,hblock⟩ := hB
  have hS : S ⊆ M.atoms := hblock.1
  have hda := Mole.deg_le_four M hM (hS hblock.2.1)
  have hdb := Mole.deg_le_four M hM (hS hblock.2.2.1)
  have hoa := outsideAt_card_add M S a
  have hob := outsideAt_card_add M S b
  have hcard := (card_le_card (boundary_subset_joints M hM hS hint)).trans
    (card_union_le (outsideAt M S a) (outsideAt M S b))
  omega

end WaveTurbulence.Vine
