/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTypeIISequence
public import WaveTurbulence.Foundations.Molecule.VineHyperEmptySequence
public import WaveTurbulence.Foundations.Molecule.VineHyperJointExclusion
public import WaveTurbulence.Foundations.Molecule.VineActualPartition
public import WaveTurbulence.Foundations.Molecule.VineCoreStemStart
import Mathlib.Tactic

/-! # No hyper-block can be contained in either bad vine type -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A type-II vine with arbitrary rung count has no hyper-block subset.
Both outer joints are excluded by degree, and all remaining atoms lie on
one full-rung sequence with those two absent external port pairs. -/
theorem typeII_no_hyperBlock_subset (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y : V} (hV : M.IsVine .II S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) : False := by
  obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
  have hl : R.k.length=1 := R.length_eq
  obtain ⟨k,hk⟩ := List.length_eq_one_iff.mp hl
  obtain ⟨Q,hu0,hv0,huN,hvN,hcovers⟩ := typeII_full_sequence R k hk
  have hj := hyperBlock_outer_joints_absent M hS hH hAS
  have habsent (i : Fin 4) (hi : i.1<2) : (R.coreAtom i).1 ∉ A := by
    rcases R.core_joint_eq hS i hi with he | he
    · simpa only [he] using hj.1
    · simpa only [he] using hj.2
  have he := hyperBlock_empty_ended_sequence M hM hH Q
    (hu0 ▸ habsent (0 : Fin 4) (by decide))
    (hv0 ▸ habsent (0 : Fin 4) (by decide))
    (huN ▸ habsent (1 : Fin 4) (by decide))
    (hvN ▸ habsent (1 : Fin 4) (by decide))
  obtain ⟨e,_he,hB⟩ := hH
  have hx : x ∈ A := hB.2.1
  have hxS := hAS hx
  have hxl : 2 ≤ R.f x := by
    by_contra hh
    have hjoint := (realization_index_lt_two_iff R hS hxS).mp (by omega)
    rcases hjoint with rfl | rfl
    · exact hj.1 hx
    · exact hj.2 hx
  obtain ⟨i,hi,hin,hxi⟩ := hcovers x hxS hxl
  rcases hxi with h | h
  · exact (he i hi hin).1 (h ▸ hx)
  · exact (he i hi hin).2 (h ▸ hx)

/-- A type-I vine has only its two degree-two outer joints and therefore
has no hyper-block subset. -/
theorem typeI_no_hyperBlock_subset (M : Molecule V D)
    {S A : Finset V} {a b x y : V} (hV : M.IsVine .I S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) : False := by
  obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
  have hj := hyperBlock_outer_joints_absent M hS hH hAS
  obtain ⟨e,_he,hB⟩ := hH
  have hx : x ∈ A := hB.2.1
  have hxS := hAS hx
  have hl := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hxS)
  have hn : (VineType.I.expand R.k).n=2 := rfl
  rw [hn] at hl
  rcases (realization_index_lt_two_iff R hS hxS).mp hl with rfl | rfl
  · exact hj.1 hx
  · exact hj.2 hx

/-- TARGET subsetvc, hyper-object exclusion for both bad outer vine types,
without any restriction on decorations, gaps or ladder lengths. -/
theorem bad_vine_no_hyperBlock_subset (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} (hbad : X.IsBad=true) {S A : Finset V} {a b x y : V}
    (hV : M.IsVine X S a b) (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) : False := by
  cases X
  · exact typeI_no_hyperBlock_subset M hV hAS hH
  · exact typeII_no_hyperBlock_subset M hM hV hAS hH
  all_goals cases hbad

end WaveTurbulence.Vine
