/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103GoodConfiguration
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103PostBridgeCut
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103SearchProgress
import Mathlib.Tactic

/-! # Actual finite-star and old-cut helpers for the good selector -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem Star3Remainder.atom_head {M : Molecule V D} {a : V} {x : D} (A : Star3Remainder M a x) :
    M.atom x = a := (Mole.mem_dartsAt M a x).mp (by rw [A.star]; simp)

theorem Star3Remainder.atom_y {M : Molecule V D} {a : V} {x : D} (A : Star3Remainder M a x) :
    M.atom A.y = a := (Mole.mem_dartsAt M a A.y).mp (by rw [A.star]; simp)

theorem Star3Remainder.atom_z {M : Molecule V D} {a : V} {x : D} (A : Star3Remainder M a x) :
    M.atom A.z = a := (Mole.mem_dartsAt M a A.z).mp (by rw [A.star]; simp)

theorem Star4Remainder.s_not_mem {M : Molecule V D} {a : V} {x y : D} (B : Star4Remainder M a x y) :
    B.s ∉ ({x,y,B.r} : Finset D) := by
  simp only [mem_insert,mem_singleton,not_or]
  exact ⟨Ne.symm B.xs,Ne.symm B.ys,Ne.symm B.rs⟩

/-- A cubic degree produces an actual ordered star, including when the
ambient dart or vertex type has no globally chosen default element. -/
theorem exists_star3_order (M : Molecule V D) (a : V) (h3 : M.deg a = 3) :
    ∃ x : D, Nonempty (Star3Remainder M a x) := by
  have hp : 0 < (M.dartsAt a).card := by change 0 < M.deg a; omega
  obtain ⟨x,hx⟩ := card_pos.mp hp
  exact ⟨x,exists_star3_remainder M h3 ((Mole.mem_dartsAt M a x).mp hx)⟩

/-- Every actual surviving dart differs from both incidences of a first
star bond. This supplies all cut/profile distinctness facts. -/
theorem retained_ne_first_incidence (M : Molecule V D) (a : V) (p : RetainedDart M {a})
    {x : D} (hx : M.atom x = a) : p.val ≠ x ∧ p.val ≠ M.mate x := by
  constructor
  · intro h
    exact p.property.1 (by simpa only [h,hx,mem_singleton])
  · intro h
    exact p.property.2 (by simpa only [h,M.mate_mate,hx,mem_singleton])

/-- A post-R bridge label is determined by the whole actual first-star
profile, using its far OLD cut. No label-uniqueness conclusion is assumed. -/
theorem firstProfileCut_of_post_bridge (M : Molecule V D) (a : V) (x : D)
    (A : Star3Remainder M a x) (p : RetainedDart M {a})
    (hp : IsBridge (eraseAtoms M {a}) p) : FirstProfileCut M x A.y A.z p.val := by
  classical
  let N := eraseAtoms M {a}
  let U := bridgeSide N (N.mate p)
  have hU : U ⊆ N.atoms := bridgeSide_subset N (N.mate p)
  have hb : boundaryDarts N U = {N.mate p} :=
    boundary_bridgeSide N _ ((isBridge_mate_iff N p).mpr hp)
  obtain ⟨hmem,hsub⟩ := boundary_old_subset_of_post_single_boundary M a U hU (N.mate p) hb
  change M.mate p.val ∈ boundaryDarts M U at hmem
  change boundaryDarts M U ⊆ {M.mate p.val} ∪ (M.dartsAt a).image M.mate at hsub
  rw [A.star,image_insert,image_insert,image_singleton] at hsub
  right
  refine ⟨U,fun b hb => (mem_sdiff.mp (hU hb)).1,hmem,?_⟩
  intro z hz
  have hh := hsub hz
  simpa only [mem_union,mem_insert,mem_singleton] using hh

end WaveTurbulence.MoleProp
