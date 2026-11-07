/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103OrdinaryStep
import Mathlib.Tactic

/-! # Actual old-star classification behind the post-R degree cases -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The old star partitions into the actual surviving darts and the
actual darts ending at the deleted atoms. -/
theorem star_eq_image_erase_union_removed (M : Molecule V D) (Y : Finset V)
    {a : V} (ha : a ∉ Y) : M.dartsAt a =
      ((eraseAtoms M Y).dartsAt a).image (fun z => z.val) ∪ removedDartsAt M Y a := by
  classical
  ext z
  constructor
  · intro hz
    have hza := (Mole.mem_dartsAt M a z).mp hz
    by_cases hm : M.atom (M.mate z) ∈ Y
    · exact mem_union_right _ (mem_filter.mpr ⟨hz,hm⟩)
    · apply mem_union_left
      exact mem_image.mpr ⟨⟨z,hza.symm ▸ ha,hm⟩,(Mole.mem_dartsAt _ a _).mpr hza,rfl⟩
  · intro hz
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      exact (Mole.mem_dartsAt M a x.val).mpr ((Mole.mem_dartsAt _ a x).mp hx)
    · exact (mem_filter.mp hz).1

/-- A unique lost dart is a unique actual old edge joining the two atoms. -/
theorem exists_shared_edge_of_removed_card_one (M : Molecule V D) (v a : V)
    (hc : (removedDartsAt M {v} a).card = 1) :
    ∃ p : D, M.atom p = v ∧ M.atom (M.mate p) = a ∧ removedDartsAt M {v} a = {M.mate p} := by
  obtain ⟨z,hz⟩ := card_eq_one.mp hc
  have hzm : z ∈ removedDartsAt M {v} a := by rw [hz]; simp
  have hh := mem_filter.mp hzm
  have hza := (Mole.mem_dartsAt M a z).mp hh.1
  have hmv : M.atom (M.mate z) = v := by simpa only [mem_singleton] using hh.2
  refine ⟨M.mate z,hmv,?_,?_⟩
  · simpa only [M.mate_mate] using hza
  · simpa only [M.mate_mate] using hz

/-- A post-degree-three atom is either an unchanged OLD degree-three
star, or an OLD degree-four star with its unique shared edge removed. -/
theorem old_star_cases_of_post_degree_three (M : Molecule V D) (hM : M.IsMolecule)
    (v a : V) (ha : a ∈ (eraseAtoms M {v}).atoms) (hpost : (eraseAtoms M {v}).deg a = 3) :
    (M.deg a = 3 ∧ M.dartsAt a = ((eraseAtoms M {v}).dartsAt a).image (fun z => z.val)) ∨
    (M.deg a = 4 ∧ ∃ p : D, M.atom p = v ∧ M.atom (M.mate p) = a ∧
      removedDartsAt M {v} a = {M.mate p} ∧ M.dartsAt a = ((eraseAtoms M {v}).dartsAt a).image (fun z => z.val) ∪ {M.mate p}) := by
  have ha' := mem_sdiff.mp ha
  have he := deg_eraseAtoms_add_removed M {v} ha'.2
  have hcap := Mole.deg_le_four M hM ha'.1
  have hs := star_eq_image_erase_union_removed M {v} ha'.2
  by_cases hc : (removedDartsAt M {v} a).card = 0
  · left
    have hempty := card_eq_zero.mp hc
    refine ⟨by omega,?_⟩
    simpa only [hempty,union_empty] using hs
  · right
    have hc1 : (removedDartsAt M {v} a).card = 1 := by omega
    obtain ⟨p,hp,hpa,hset⟩ := exists_shared_edge_of_removed_card_one M v a hc1
    exact ⟨by omega,p,hp,hpa,hset,by simpa only [hset] using hs⟩

/-- Under source simplicity and minimum degree three, a post-degree-two
atom was OLD degree three and has exactly one actual shared edge. -/
theorem old_shared_star_of_post_degree_two (M : Molecule V D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    (hmin : ∀ a ∈ M.atoms, 3 ≤ M.deg a)
    (v a : V) (ha : a ∈ (eraseAtoms M {v}).atoms) (hpost : (eraseAtoms M {v}).deg a = 2) :
    M.deg a = 3 ∧ ∃ p : D, M.atom p = v ∧ M.atom (M.mate p) = a ∧
      removedDartsAt M {v} a = {M.mate p} ∧ M.dartsAt a = ((eraseAtoms M {v}).dartsAt a).image (fun z => z.val) ∪ {M.mate p} := by
  have ha' := mem_sdiff.mp ha
  have hav : a ≠ v := by simpa only [mem_singleton] using ha'.2
  have he := deg_eraseAtoms_add_removed M {v} ha'.2
  have hlo := hmin a ha'.1
  have hhi := degree_erase_singleton_add_one_ge M hsimple hav
  have hc1 : (removedDartsAt M {v} a).card = 1 := by omega
  obtain ⟨p,hp,hpa,hset⟩ := exists_shared_edge_of_removed_card_one M v a hc1
  have hs := star_eq_image_erase_union_removed M {v} ha'.2
  exact ⟨by omega,p,hp,hpa,hset,by simpa only [hset] using hs⟩

/-- The unique actually removed edge identifies the repeated-label case
without assuming that two selected first-star labels are distinct. -/
theorem first_edge_eq_of_unique_removed_star (M : Molecule V D) {v a : V} {p q : D}
    (hset : removedDartsAt M {v} a = {M.mate p}) (hq : M.atom q = v)
    (hqa : M.atom (M.mate q) = a) : q = p := by
  have hh : M.mate q ∈ removedDartsAt M {v} a := by
    apply mem_filter.mpr
    exact ⟨(Mole.mem_dartsAt M a _).mpr hqa,by simpa only [M.mate_mate,hq,mem_singleton]⟩
  rw [hset] at hh
  exact Mole.mate_injective M (mem_singleton.mp hh)

end WaveTurbulence.MoleProp
