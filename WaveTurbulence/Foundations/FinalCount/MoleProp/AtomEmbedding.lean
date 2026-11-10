/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleErasure
public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeCount
public import WaveTurbulence.Foundations.Molecule.MoleculeComponents
import Mathlib.Tactic

/-! # Adding fresh atom names preserves the genuine molecular problem

The fresh-name lift used by beta cuts is a literal injection of atom
names; darts and their labels stay unchanged. Source parameters extend
only off the actual image, where no source equation is imposed.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V W D : Type*} [DecidableEq V] [DecidableEq W] [Fintype D] [DecidableEq D]

def mapAtoms (M : Molecule V D) (f : V ↪ W) : Molecule W D where
  atoms := M.atoms.map f
  atom x := f (M.atom x)
  mate := M.mate
  out := M.out
  atom_mem x := mem_map.mpr ⟨M.atom x,M.atom_mem x,rfl⟩
  mate_mate := M.mate_mate
  mate_ne := M.mate_ne
  out_mate := M.out_mate

theorem mapAtoms_dartsAt (M : Molecule V D) (f : V ↪ W) (a : V) :
    (mapAtoms M f).dartsAt (f a) = M.dartsAt a := by
  ext x
  simp only [Mole.mem_dartsAt,mapAtoms,f.injective.eq_iff]

theorem mapAtoms_adj (M : Molecule V D) (f : V ↪ W) (a b : V) :
    (mapAtoms M f).Adj (f a) (f b) ↔ M.Adj a b := by
  constructor
  · rintro ⟨x,hxa,hxb⟩
    exact ⟨x,f.injective hxa,f.injective hxb⟩
  · rintro ⟨x,hxa,hxb⟩
    exact ⟨x,congrArg f hxa,congrArg f hxb⟩

theorem mapAtoms_sameComponent (M : Molecule V D) (f : V ↪ W) {a b : V}
    (h : M.SameComponent a b) : (mapAtoms M f).SameComponent (f a) (f b) := by
  induction h with
  | rel a b hab => exact Relation.EqvGen.rel _ _ ((mapAtoms_adj M f a b).mpr hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem mapAtoms_isMolecule (M : Molecule V D) (f : V ↪ W) (hM : M.IsMolecule) :
    (mapAtoms M f).IsMolecule := by
  constructor
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := mem_map.mp ha
    change (((mapAtoms M f).dartsAt (f b)).filter (fun x => M.out x = true)).card ≤ 2 ∧
      (((mapAtoms M f).dartsAt (f b)).filter (fun x => M.out x = false)).card ≤ 2
    rw [mapAtoms_dartsAt]
    exact hM.1 b hb
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := mem_map.mp ha
    obtain ⟨z,hz,hbz,hz4⟩ := hM.2 b hb
    refine ⟨f z,mem_map.mpr ⟨z,hz,rfl⟩,mapAtoms_sameComponent M f hbz,?_⟩
    simpa only [Molecule.deg,mapAtoms_dartsAt] using hz4

theorem mapAtoms_numComponents (M : Molecule V D) (f : V ↪ W) :
    (mapAtoms M f).numComponents = M.numComponents := by
  classical
  let g : {a // a ∈ M.atoms} → {b // b ∈ (mapAtoms M f).atoms} :=
    fun a => ⟨f a.val,mem_map.mpr ⟨a.val,a.property,rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro a b he
      exact Subtype.ext (f.injective (congrArg Subtype.val he))
    · intro b
      obtain ⟨a,ha,he⟩ := mem_map.mp b.property
      exact ⟨⟨a,ha⟩,Subtype.ext he⟩
  let e := Equiv.ofBijective g hg
  have hrel : ∀ a b, M.Adj a.val b.val ↔ (mapAtoms M f).Adj (e a).val (e b).val := by
    intro a b
    exact (mapAtoms_adj M f a.val b.val).symm
  have hh := Nat.card_congr (Quot.congr
    (ra := fun a b : {a // a ∈ M.atoms} => M.Adj a.val b.val)
    (rb := fun a b : {a // a ∈ (mapAtoms M f).atoms} => (mapAtoms M f).Adj a.val b.val) e hrel)
  exact hh.symm

theorem mapAtoms_circuitRank (M : Molecule V D) (f : V ↪ W) :
    (mapAtoms M f).circuitRank = M.circuitRank := by
  have hV : (mapAtoms M f).atoms.card = M.atoms.card := card_map _
  have hE : (mapAtoms M f).bonds = M.bonds := rfl
  unfold Molecule.circuitRank
  rw [mapAtoms_numComponents,hV,hE]

end WaveTurbulence.MoleProp
