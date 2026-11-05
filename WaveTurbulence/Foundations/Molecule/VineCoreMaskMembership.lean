/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreMasks
public import WaveTurbulence.Foundations.Molecule.VineMaskedDegrees
public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
public import WaveTurbulence.Foundations.Molecule.VineBondRestriction
import Mathlib.Tactic

/-! # Reading finite core masks as actual atom membership -/

public section
namespace WaveTurbulence.Vine

/-- Equal finite membership masks give equal membership at every core
index, even when the two sets also contain newly allocated atom labels. -/
theorem coreMaskVector_membership_iff (X : VineType) {U W : Finset ℕ}
    (he : coreMaskVector X (membershipMask U)=coreMaskVector X (membershipMask W))
    (i : ℕ) (hi : i<X.template.n) : i ∈ U ↔ i ∈ W := by
  have hh := List.map_inj_left.mp he i (List.mem_range.mpr hi)
  by_cases hu : i ∈ U <;> by_cases hw : i ∈ W <;> simp_all [membershipMask]

variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A computed core mask identifies actual membership for every old atom
inside the source realization, with no assumption on fresh atom membership. -/
theorem VineRealization.core_membership_profile {M : Molecule V D} {X : VineType}
    {S A : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hAS : A ⊆ S) (W : Finset ℕ)
    (he : coreMaskVector X (membershipMask (A.image R.f))=coreMaskVector X (membershipMask W)) :
    ∀ v ∈ S,R.f v<X.template.n → (v ∈ A ↔ R.f v ∈ W) := by
  intro v hv hi
  rw [← mem_image_iff_of_injOn hAS R.f R.injOn hv]
  exact coreMaskVector_membership_iff X he (R.f v) hi

end WaveTurbulence.Vine
