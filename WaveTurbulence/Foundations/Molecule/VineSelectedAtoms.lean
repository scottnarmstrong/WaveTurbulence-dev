/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
import Mathlib.Tactic

/-! # Actual atom sets selected by finite template label sets -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Pull back a finite label set inside the actual outer vine. -/
@[expose] def VineRealization.selectedAtoms {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (W : Finset ℕ) : Finset V :=
  S.filter (fun v => R.f v ∈ W)

/-- The selected actual atoms have exactly the labels in the available
finite template range. -/
theorem VineRealization.image_selectedAtoms {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (W : Finset ℕ) :
    (R.selectedAtoms W).image R.f=W ∩ range (X.expand R.k).n := by
  rw [← R.image_eq]
  ext i
  constructor
  · intro hi
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
    have hh := mem_filter.mp hv
    exact mem_inter.mpr ⟨hh.2,mem_image_of_mem R.f hh.1⟩
  · intro hi
    obtain ⟨hiW,hiS⟩ := mem_inter.mp hi
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hiS
    exact mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,hiW⟩,rfl⟩

/-- Selecting an available label set preserves its exact cardinality. -/
theorem VineRealization.card_selectedAtoms {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (W : Finset ℕ)
    (hW : W ⊆ range (X.expand R.k).n) : (R.selectedAtoms W).card=W.card := by
  have hi : Set.InjOn R.f (R.selectedAtoms W) := by
    intro u hu v hv he
    exact R.injOn (mem_filter.mp hu).1 (mem_filter.mp hv).1 he
  rw [← card_image_of_injOn hi,R.image_selectedAtoms,inter_eq_left.mpr hW]

end WaveTurbulence.Vine
