/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniqueSingleNeighbor
public import WaveTurbulence.Foundations.FinalCount.Algorithm.PairBondEnumeration
public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
import Mathlib.Tactic

/-! # A source special bond is the sole single bond at either endpoint -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem special_single_partner_left (M : Molecule V D) (hno : AppbNoLoops M)
    {x : D} (hs : AppbSpecial M x) {b : V} (hne : M.atom x ≠ b)
    (hm : M.bondsBetween (M.atom x) b = 1) : b = M.atom (M.mate x) := by
  obtain ⟨_,hdeg,_,c,hc,d,hd,hcd,hca,hcb,hda,hdb,hcentral,hdouble,_⟩ := hs
  exact single_neighbor_unique_of_double M (hno x) hca.symm hcb.symm hne
    hdeg hcentral hdouble hm

theorem special_single_partner_right (M : Molecule V D) (hno : AppbNoLoops M)
    {x : D} (hs : AppbSpecial M x) {b : V} (hne : M.atom (M.mate x) ≠ b)
    (hm : M.bondsBetween (M.atom (M.mate x)) b = 1) : b = M.atom x := by
  obtain ⟨_,_,hdeg,c,hc,d,hd,hcd,hca,hcb,hda,hdb,hcentral,_,hdouble⟩ := hs
  have hcentral' : M.bondsBetween (M.atom (M.mate x)) (M.atom x) = 1 :=
    (bondsBetween_symm M _ _).trans hcentral
  exact single_neighbor_unique_of_double M (Ne.symm (hno x)) hdb.symm hda.symm hne
    hdeg hcentral' hdouble hm

theorem special_single_incidence_ends (M : Molecule V D) (hno : AppbNoLoops M)
    {x : D} (hs : AppbSpecial M x) {a b : V} (hab : a ≠ b)
    (hm : M.bondsBetween a b = 1)
    (hinc : a = M.atom x ∨ a = M.atom (M.mate x)) : s(a,b) = M.ends x := by
  rcases hinc with rfl | rfl
  · have hb := special_single_partner_left M hno hs hab hm
    rw [hb]
    rfl
  · have hb := special_single_partner_right M hno hs hab hm
    rw [hb]
    exact Sym2.eq_swap

theorem single_outgoing_eq (M : Molecule V D) {x y : D} (hx : M.out x = true)
    (hy : M.out y = true) (hend : M.ends x = M.ends y)
    (hm : M.bondsBetween (M.atom y) (M.atom (M.mate y)) = 1) : x = y := by
  classical
  have hcard : (parallelBonds M (M.atom y) (M.atom (M.mate y))).card ≤ 1 := hm.le
  apply card_le_one.mp hcard x ?_ y ?_
  · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hx⟩,hend⟩
  · exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hy⟩,rfl⟩

end WaveTurbulence.Mole.AppbAlgorithm
