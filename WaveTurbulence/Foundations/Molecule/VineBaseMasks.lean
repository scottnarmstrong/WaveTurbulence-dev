/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRealizationDegrees
public import WaveTurbulence.Foundations.Molecule.VineCoreClassification
public import WaveTurbulence.Foundations.Molecule.VineMaskedDegrees
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic

/-! # Actual nested block masks in the eight unexpanded vine cores -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Transport the actual selected-group degree profile into the checked
finite core table. This helper is restricted to the zero-extra-rung case. -/
theorem base_mask_of_degrees {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (hk : R.k=List.replicate X.template.slots.length 0)
    {A : Finset V} (hAS : A ⊆ S) (kind : CoreKind) (x y : V) (hx : x ∈ A) (hy : y ∈ A)
    (hne : x ≠ y) (hdegree : ∀ v ∈ A,
      M.degIn A v=if v=x ∨ v=y then kind.jointDegree else 4) :
    coreMaskVector X (membershipMask (A.image R.f)) ∈ coreMaskCandidates X kind := by
  let U := A.image R.f
  have hfx : R.f x<X.template.n := by
    have hh := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f (hAS hx))
    simpa only [hk,expand_zero_rungs] using hh
  have hfy : R.f y<X.template.n := by
    have hh := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f (hAS hy))
    simpa only [hk,expand_zero_rungs] using hh
  have hfne : R.f x ≠ R.f y := fun h => hne (R.injOn (hAS hx) (hAS hy) h)
  apply coreMask_exhaustive_unordered X kind (membershipMask U) (R.f x) (R.f y) hfx hfy hfne
  · have hh : R.f x ∈ U := mem_image_of_mem R.f hx
    simp only [membershipMask,hh,ite_true]
  · have hh : R.f y ∈ U := mem_image_of_mem R.f hy
    simp only [membershipMask,hh,ite_true]
  · intro i _hi
    unfold membershipMask
    split_ifs <;> omega
  · intro i _hi hm
    have hiU : i ∈ U := by
      by_contra hh
      simp only [membershipMask,hh,ite_false,Nat.zero_ne_one] at hm
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hiU
    rw [coreDegree_membershipMask X U (R.f v) (mem_image_of_mem R.f hv)]
    have hd := R.subgroup_degree hAS (hAS hv)
    rw [hk,expand_zero_rungs] at hd
    rw [← hd]
    have hxv : R.f v=R.f x ↔ v=x := ⟨fun h => R.injOn (hAS hv) (hAS hx) h,congrArg R.f⟩
    have hyv : R.f v=R.f y ↔ v=y := ⟨fun h => R.injOn (hAS hv) (hAS hy) h,congrArg R.f⟩
    simpa only [hxv,hyv] using hdegree v hv

/-- Every actual nested block in an unexpanded vine has one of the checked
base-core degree masks. No mask-classification premise is assumed. -/
theorem base_block_mask_exhaustive {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hk : R.k=List.replicate X.template.slots.length 0)
    {A : Finset V} {x y : V} (hAS : A ⊆ S) (hA : M.IsBlock A x y) :
    coreMaskVector X (membershipMask (A.image R.f)) ∈ coreMaskCandidates X .block := by
  apply base_mask_of_degrees R hk hAS .block x y hA.2.1 hA.2.2.1 hA.2.2.2.1
  obtain ⟨hx,hy⟩ := Mole.block_joint_degrees M hA
  intro v hv
  split_ifs with h
  · rcases h with rfl | rfl
    · exact hx
    · exact hy
  · have hn : v ≠ x ∧ v ≠ y := not_or.mp h
    exact hA.2.2.2.2.2.2.2.2.1 v hv hn.1 hn.2

/-- The corresponding base-core table also classifies actual nested
hyper-block degree masks. -/
theorem base_hyperBlock_mask_exhaustive [DecidableEq D] {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hk : R.k=List.replicate X.template.slots.length 0)
    {A : Finset V} {x y : V} (hAS : A ⊆ S) (hA : Mole.IsHyperBlock M A x y) :
    coreMaskVector X (membershipMask (A.image R.f)) ∈ coreMaskCandidates X .hyper := by
  obtain ⟨hx,hy,hint⟩ := Mole.hyperBlock_degrees M hA
  obtain ⟨e,_he,hB⟩ := hA
  apply base_mask_of_degrees R hk hAS .hyper x y hB.2.1 hB.2.2.1 hB.2.2.2.1
  intro v hv
  split_ifs with h
  · rcases h with rfl | rfl
    · exact hx
    · exact hy
  · have hn : v ≠ x ∧ v ≠ y := not_or.mp h
    exact hint v hv hn.1 hn.2

end WaveTurbulence.Vine
