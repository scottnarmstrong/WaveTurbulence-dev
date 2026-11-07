/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.CommonParameters
public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-! # Atom erasure preserves the actual molecule axioms -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Restricting the dart carrier can only decrease each oriented local count. -/
theorem card_filtered_dartsAt_erase_le (M : Molecule V D) (Y : Finset V) (z : V)
    (p : D → Prop) [DecidablePred p] :
    (((eraseAtoms M Y).dartsAt z).filter (fun x => p x.val)).card ≤
      ((M.dartsAt z).filter p).card := by
  classical
  have hs : ((((eraseAtoms M Y).dartsAt z).filter (fun x => p x.val)).image
      (fun x => x.val)) ⊆ (M.dartsAt z).filter p := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    obtain ⟨ha,hp⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M z a.val).mpr ((mem_filter.mp ha).2),hp⟩
  have hc := card_le_card hs
  rw [card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

/-- A surviving degree-four atom lost no dart, so every old adjacent atom
also survives and is still adjacent in the actual erased molecule. -/
theorem adj_erase_of_surviving_four (M : Molecule V D) (hM : M.IsMolecule) (Y : Finset V)
    {a b : V} (ha : a ∈ (eraseAtoms M Y).atoms) (hfour : (eraseAtoms M Y).deg a = 4)
    (hab : M.Adj a b) : b ∈ (eraseAtoms M Y).atoms ∧ (eraseAtoms M Y).Adj a b := by
  obtain ⟨x,hxa,hxb⟩ := hab
  have haY := (mem_sdiff.mp ha).2
  have he := deg_eraseAtoms_add_removed M Y haY
  have hcap := Mole.deg_le_four M hM (mem_sdiff.mp ha).1
  have hempty : removedDartsAt M Y a = ∅ := card_eq_zero.mp (by omega)
  have hbY : b ∉ Y := by
    intro hb
    have hx : x ∈ removedDartsAt M Y a := mem_filter.mpr
      ⟨(Mole.mem_dartsAt M a x).mpr hxa,hxb.symm ▸ hb⟩
    rw [hempty] at hx
    simpa using hx
  have hxY : M.atom x ∉ Y := hxa.symm ▸ haY
  have hmxY : M.atom (M.mate x) ∉ Y := hxb.symm ▸ hbY
  exact ⟨mem_sdiff.mpr ⟨hxb ▸ M.atom_mem (M.mate x),hbY⟩,
    ⟨⟨x,hxY,hmxY⟩,hxa,hxb⟩⟩

/-- Deleting any finite collection of atoms preserves both oriented degree
bounds and nonsaturation. In particular the empty residual molecule is allowed. -/
theorem isMolecule_eraseAtoms (M : Molecule V D) (hM : M.IsMolecule) (Y : Finset V) :
    (eraseAtoms M Y).IsMolecule := by
  classical
  constructor
  · intro z hz
    have ho := card_filtered_dartsAt_erase_le M Y z (fun x => M.out x = true)
    have hi := card_filtered_dartsAt_erase_le M Y z (fun x => M.out x = false)
    exact ⟨ho.trans (hM.1 z (mem_sdiff.mp hz).1).1,hi.trans (hM.1 z (mem_sdiff.mp hz).1).2⟩
  · intro z hz
    by_contra hn
    have hsat (a : V) (ha : a ∈ (eraseAtoms M Y).atoms)
        (hza : (eraseAtoms M Y).SameComponent z a) : (eraseAtoms M Y).deg a = 4 := by
      by_contra hne
      exact hn ⟨a,ha,hza,hne⟩
    let C := fun a => a ∈ (eraseAtoms M Y).atoms ∧ (eraseAtoms M Y).SameComponent z a
    have hclosed (a b : V) (hab : M.Adj a b) (ha : C a) : C b := by
      obtain ⟨hb,hab'⟩ := adj_erase_of_surviving_four M hM Y ha.1 (hsat a ha.1 ha.2) hab
      exact ⟨hb,Relation.EqvGen.trans _ _ _ ha.2 (Relation.EqvGen.rel _ _ hab')⟩
    have hpath (a b : V) (hab : M.SameComponent a b) : C a ↔ C b := by
      induction hab with
      | rel a b h => exact ⟨hclosed a b h,hclosed b a (Mole.adj_symmetric M h)⟩
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
    obtain ⟨u,hu,hzu,hu4⟩ := hM.2 z (mem_sdiff.mp hz).1
    have huC := (hpath z u hzu).mp ⟨hz,Relation.EqvGen.refl z⟩
    have he := deg_eraseAtoms_add_removed M Y (mem_sdiff.mp huC.1).2
    have hfour := hsat u huC.1 huC.2
    have hcap := Mole.deg_le_four M hM hu
    apply hu4
    omega

end WaveTurbulence.Degen
