/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeOneBridge
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # Exact two-atom cut size and the excluded double 3–2 bond -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem boundary_pair_card (M : Molecule V D) (hno : AppbNoLoops M)
    {a b : V} (hab : a ≠ b) :
    (Degen.boundaryDarts M {a,b}).card + 2*M.bondsBetween a b = M.deg a+M.deg b := by
  classical
  let cut := fun v => (M.dartsAt v).filter fun x => M.atom (M.mate x) ∉ ({a,b} : Finset V)
  have hset : Degen.boundaryDarts M {a,b} = cut a ∪ cut b := by
    ext x
    simp only [Degen.boundaryDarts,cut,Molecule.dartsAt,mem_filter,mem_univ,
      true_and,mem_insert,mem_singleton,mem_union]
    tauto
  have hdis : Disjoint (cut a) (cut b) := by
    apply disjoint_left.mpr
    intro x hx hy
    have ha := (mem_filter.mp (mem_filter.mp hx).1).2
    have hb := (mem_filter.mp (mem_filter.mp hy).1).2
    exact hab (ha.symm.trans hb)
  have hlocal (v : V) (hv : v ∈ ({a,b} : Finset V)) :
      (cut v).card+M.degIn {a,b} v = M.deg v := by
    have hh := card_filter_add_card_filter_not (s := M.dartsAt v)
      (fun x => M.atom (M.mate x) ∈ ({a,b} : Finset V))
    have hi : (M.dartsAt v).filter (fun x => M.atom (M.mate x) ∈ ({a,b} : Finset V)) =
        (M.dartsAt v).filter (M.InGroup {a,b}) := by
      ext x
      simp only [mem_filter,Molecule.InGroup]
      constructor
      · rintro ⟨hx,hm⟩
        exact ⟨hx,by simpa only [(mem_dartsAt M v x).mp hx] using hv,hm⟩
      · rintro ⟨hx,_,hm⟩; exact ⟨hx,hm⟩
    rw [hi] at hh
    change M.degIn {a,b} v + (cut v).card = M.deg v at hh
    omega
  have ha := hlocal a (by simp)
  have hb := hlocal b (by simp)
  have hia := degIn_pair_eq_bondsBetween M hab (fun x hx => fun hh => hno x (hx.trans hh.symm))
  have hib := degIn_pair_eq_bondsBetween M hab.symm (fun x hx => fun hh => hno x (hx.trans hh.symm))
  rw [Finset.pair_comm,bondsBetween_symm M b a] at hib
  rw [hset,card_union_of_disjoint hdis]
  omega

/-- A double bond between degrees three and two forces a bridge, so it
cannot reach the single-bond figures of source rule five. -/
theorem exists_bridge_of_three_two_double (M : Molecule V D) (hno : AppbNoLoops M)
    {a b : V} (hab : a ≠ b) (ha : M.deg a = 3) (hb : M.deg b = 2)
    (hm : M.bondsBetween a b = 2) : ∃ e : D,Degen.IsBridge M e := by
  have hh := boundary_pair_card M hno hab
  have hc : (Degen.boundaryDarts M {a,b}).card = 1 := by omega
  obtain ⟨e,he⟩ := card_eq_one.mp hc
  exact ⟨e,Degen.isBridge_of_single_boundary M {a,b} he⟩

end WaveTurbulence.Mole.AppbAlgorithm
