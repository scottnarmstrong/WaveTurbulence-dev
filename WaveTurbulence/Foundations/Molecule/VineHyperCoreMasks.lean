/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperCoreCut
public import WaveTurbulence.Foundations.Molecule.VineCoreCutClassification
public import WaveTurbulence.Foundations.Molecule.VineHyperCoreNonempty
public import WaveTurbulence.Foundations.Molecule.VineActualPartition
import Mathlib.Tactic

/-! # Arbitrary-rung hyper-block subsets have the same core masks as the finite cores -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, arbitrary-rung core classification: every actual
hyper-block subset has one of the nonempty hyper-core masks. The empty mask
is excluded using all slot allocation intervals, and all other masks are
excluded by the exact two-boundary-bond budget. -/
theorem hyperBlock_core_mask_exhaustive (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S A : Finset V} {a b x y : V}
    (R : VineRealization M X S a b) (hS : M.IsBlock S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) :
    coreMaskVector X (membershipMask (A.image R.f)) ∈ coreMaskCandidates X .hyper := by
  have hj := hyperBlock_outer_joints_absent M hS hH hAS
  have hout (i : ℕ) (hi : i<2) : i ∉ A.image R.f := by
    intro him
    obtain ⟨z,hz,hzi⟩ := mem_image.mp him
    have hzl : R.f z<2 := by omega
    rcases (realization_index_lt_two_iff R hS (hAS hz)).mp hzl with he | he
    · exact hj.1 (he ▸ hz)
    · exact hj.2 (he ▸ hz)
  have hc := core_cut_mask_exhaustive X (A.image R.f)
    (hout 0 (by decide)) (hout 1 (by decide))
    (R.hyperBlock_core_cut_le_two M hM hS hAS hH)
  rcases List.mem_cons.mp hc with hempty | hc
  · obtain ⟨z,hz,hzi⟩ := hyperBlock_has_core_label M hM R hAS hH
    have hmask : membershipMask (A.image R.f) (R.f z)=1 := by
      simp only [membershipMask,mem_image_of_mem R.f hz,ite_true]
    have hone : 1 ∈ coreMaskVector X (membershipMask (A.image R.f)) := by
      exact List.mem_map.mpr ⟨R.f z,List.mem_range.mpr hzi,hmask⟩
    rw [hempty] at hone
    have hbad := (List.mem_replicate.mp hone).2
    omega
  · exact hc

/-- Types I--IV contain no hyper-block subset, even after arbitrary rung
insertions. This is stronger than the decorated SG containment exclusion. -/
theorem noncap_vine_no_hyperBlock_subset (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} (hX : X=.I ∨ X=.II ∨ X=.III ∨ X=.IV)
    {S A : Finset V} {a b x y : V} (hV : M.IsVine X S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) : False := by
  obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
  have hm := hyperBlock_core_mask_exhaustive M hM R hS hAS hH
  rcases hX with rfl | rfl | rfl | rfl <;> exact List.not_mem_nil hm

end WaveTurbulence.Vine
