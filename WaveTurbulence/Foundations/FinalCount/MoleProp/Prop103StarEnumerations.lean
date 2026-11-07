/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103FourStarDirections
import Mathlib.Tactic

/-! # Internally chosen actual star enumerations for the good selector -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An actual ordered cubic star with its first incidence prescribed. -/
structure Star3Remainder (M : Molecule V D) (a : V) (x : D) where
  y : D
  z : D
  xy : x ≠ y
  xz : x ≠ z
  yz : y ≠ z
  star : M.dartsAt a = {x,y,z}

/-- An actual ordered quartic star with its first two incidences prescribed. -/
structure Star4Remainder (M : Molecule V D) (a : V) (x y : D) where
  r : D
  s : D
  xy : x ≠ y
  xr : x ≠ r
  xs : x ≠ s
  yr : y ≠ r
  ys : y ≠ s
  rs : r ≠ s
  star : M.dartsAt a = {x,y,r,s}

/-- A prescribed actual dart of a cubic star extends to its complete
ordered actual star. -/
theorem exists_star3_remainder (M : Molecule V D) {a : V} {x : D}
    (h3 : M.deg a = 3) (hx : M.atom x = a) : Nonempty (Star3Remainder M a x) := by
  classical
  have hxm := (Mole.mem_dartsAt M a x).mpr hx
  have hc : ((M.dartsAt a).erase x).card = 2 := by
    rw [card_erase_of_mem hxm]
    change (M.dartsAt a).card = 3 at h3
    omega
  obtain ⟨y,z,hyz,hset⟩ := card_eq_two.mp hc
  have hy : y ∈ (M.dartsAt a).erase x := by rw [hset]; simp
  have hz : z ∈ (M.dartsAt a).erase x := by rw [hset]; simp
  have hxy := Ne.symm (mem_erase.mp hy).1
  have hxz := Ne.symm (mem_erase.mp hz).1
  refine ⟨⟨y,z,hxy,hxz,hyz,?_⟩⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨hxm,(mem_erase.mp hy).2,(mem_erase.mp hz).2⟩
  · change M.deg a ≤ _
    simp [h3,hxy,hxz,hyz]

/-- Two distinct actual prescribed darts of a cubic star leave one
actual third incidence. -/
theorem exists_third_of_star3 (M : Molecule V D) {a : V} {x y : D}
    (h3 : M.deg a = 3) (hx : M.atom x = a) (hy : M.atom y = a) (hxy : x ≠ y) :
    ∃ z, x ≠ z ∧ y ≠ z ∧ M.dartsAt a = {x,y,z} := by
  classical
  have hs : {x,y} ⊆ M.dartsAt a := by
    simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨(Mole.mem_dartsAt M a x).mpr hx,(Mole.mem_dartsAt M a y).mpr hy⟩
  have hc : ((M.dartsAt a) \ {x,y}).card = 1 := by
    have hh := card_sdiff_add_card_eq_card hs
    rw [card_pair hxy] at hh
    change (M.dartsAt a).card = 3 at h3
    omega
  obtain ⟨z,hz⟩ := card_eq_one.mp hc
  have hzm : z ∈ (M.dartsAt a) \ {x,y} := by rw [hz]; simp
  have hz' := mem_sdiff.mp hzm
  have hxz : x ≠ z := fun h => hz'.2 (by simp [← h])
  have hyz : y ≠ z := fun h => hz'.2 (by simp [← h])
  refine ⟨z,hxz,hyz,?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨(Mole.mem_dartsAt M a x).mpr hx,(Mole.mem_dartsAt M a y).mpr hy,hz'.1⟩
  · change M.deg a ≤ _
    simp [h3,hxy,hxz,hyz]

/-- Prescribed distinct incidences at a quartic star extend to its actual
ordered complete star. -/
theorem exists_star4_remainder (M : Molecule V D) {a : V} {x y : D}
    (h4 : M.deg a = 4) (hx : M.atom x = a) (hy : M.atom y = a) (hxy : x ≠ y) :
    Nonempty (Star4Remainder M a x y) := by
  obtain ⟨r,s,hr,hs,hxr,hxs,hyr,hys,hrs,hstar⟩ := exists_remaining_pair_of_degree_four M h4 hx hy hxy
  exact ⟨⟨r,s,hxy,hxr,hxs,hyr,hys,hrs,hstar⟩⟩

end WaveTurbulence.MoleProp
