/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineMaskCardinality
public import WaveTurbulence.Foundations.Molecule.VineRealizationAdjacency
import Mathlib.Tactic

/-! # Complete masks determine actual selected atom sets -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A full membership vector on the finite range determines its subset. -/
theorem coreMaskVector_injective (X : VineType) {U W : Finset ℕ}
    (hU : U ⊆ range X.template.n) (hW : W ⊆ range X.template.n)
    (he : coreMaskVector X (membershipMask U)=coreMaskVector X (membershipMask W)) : U=W := by
  have hm := List.map_inj_left.mp he
  ext i
  by_cases hi : i<X.template.n
  · have hh := hm i (List.mem_range.mpr hi)
    by_cases hu : i ∈ U <;> by_cases hw : i ∈ W <;> simp_all [membershipMask]
  · have hu : i ∉ U := fun h => hi (mem_range.mp (hU h))
    have hw : i ∉ W := fun h => hi (mem_range.mp (hW h))
    simp only [hu,hw]

/-- The actual subgroup image is exactly the finite set encoded by its
complete base-core mask. -/
theorem VineRealization.base_image_eq_of_mask {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hk : R.k=List.replicate X.template.slots.length 0)
    {A : Finset V} (hAS : A ⊆ S) (W : Finset ℕ) (hW : W ⊆ range X.template.n)
    (he : coreMaskVector X (membershipMask (A.image R.f))=coreMaskVector X (membershipMask W)) :
    A.image R.f=W := by
  apply coreMaskVector_injective X _ hW he
  intro i hi
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
  have hh := R.image_eq ▸ mem_image_of_mem R.f (hAS hv)
  simpa only [hk,expand_zero_rungs] using hh

/-- Injectivity of the pinned realization identifies selected membership
with membership of its image, for every atom of the outer vine. -/
theorem VineRealization.mem_iff_image {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} (hAS : A ⊆ S) {v : V} (hv : v ∈ S) :
    v ∈ A ↔ R.f v ∈ A.image R.f := by
  constructor
  · exact mem_image_of_mem R.f
  · intro h
    obtain ⟨u,hu,he⟩ := mem_image.mp h
    exact R.injOn (hAS hu) hv he ▸ hu

end WaveTurbulence.Vine
