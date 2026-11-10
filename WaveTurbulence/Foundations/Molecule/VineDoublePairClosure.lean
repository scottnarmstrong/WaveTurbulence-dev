/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperRungMembership
public import WaveTurbulence.Foundations.Molecule.VineBoundaryCounts
import Mathlib.Tactic

/-! # Double bonds cannot be split by hyper-blocks (TARGET subsetvc) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Two actual distinct incidences at x with common neighbor y. -/
structure TwoIncidences (M : Molecule V D) (x y : V) where
  dart : Fin 2 → D
  injective : Function.Injective dart
  atom_eq : ∀ i,M.atom (dart i)=x
  neighbor_eq : ∀ i,M.atom (M.mate (dart i))=y

/-- The mate involution records the same two incidences at the other end. -/
@[expose] def TwoIncidences.mates {M : Molecule V D} {x y : V}
    (R : TwoIncidences M x y) : TwoIncidences M y x where
  dart := fun i => M.mate (R.dart i)
  injective := (Mole.mate_injective M).comp R.injective
  atom_eq := R.neighbor_eq
  neighbor_eq := by intro i; rw [M.mate_mate]; exact R.atom_eq i

/-- If two incidences leave a group, at most two can remain inside it. -/
theorem twoOutside_degree_le_two (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {x y : V} (R : TwoIncidences M x y) (hy : y ∉ S) :
    M.degIn S x≤2 := by
  have hsub : univ.image R.dart ⊆ outsideAt M S x := by
    intro z hz
    obtain ⟨i,_hi,rfl⟩ := mem_image.mp hz
    apply mem_filter.mpr
    refine ⟨(Mole.mem_dartsAt M x _).mpr (R.atom_eq i),?_⟩
    intro hg
    exact hy (R.neighbor_eq i ▸ hg.2)
  have hc := card_le_card hsub
  rw [card_image_of_injective _ R.injective,card_univ,Fintype.card_fin] at hc
  have hsplit := outsideAt_card_add M S x
  have hxM : x ∈ M.atoms := R.atom_eq 0 ▸ M.atom_mem (R.dart 0)
  have htotal := Mole.deg_le_four M hM hxM
  omega

/-- A block can split a double-bond pair only at one of its joints. -/
theorem block_split_double_is_joint (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b x y : V} (hB : M.IsBlock S a b)
    (R : TwoIncidences M x y) (hx : x ∈ S) (hy : y ∉ S) : x=a ∨ x=b := by
  by_contra h
  have hn : x ≠ a ∧ x ≠ b := not_or.mp h
  have hd := hB.2.2.2.2.2.2.2.2.1 x hx hn.1 hn.2
  have hhi := twoOutside_degree_le_two M hM R hy
  omega

end WaveTurbulence.Vine
