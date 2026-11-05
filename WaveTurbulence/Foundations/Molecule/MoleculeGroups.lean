/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-!
# Actual atomic groups and block degrees

TARGET `defmol` and `defblock` (L1295, L1328): an atomic group carries
exactly the bonds with both endpoints in the group. Its induced half-edge
carrier retains all multiplicities and self-loops.
-/

public section

namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- The actual induced atomic group, with the unchanged bond involution. -/
@[expose] def induced (S : Finset V) : Molecule V {x : D // M.InGroup S x} where
  atoms := S
  atom := fun x => M.atom x.1
  mate := fun x => ⟨M.mate x.1,x.2.2,by simpa only [M.mate_mate] using x.2.1⟩
  out := fun x => M.out x.1
  atom_mem := fun x => x.2.1
  mate_mate := fun x => Subtype.ext (M.mate_mate x.1)
  mate_ne := fun x h => M.mate_ne x.1 (congrArg Subtype.val h)
  out_mate := fun x => M.out_mate x.1

/-- The induced carrier's actual degree is the draft's degree within S. -/
theorem induced_deg (S : Finset V) (v : V) : (induced M S).deg v = M.degIn S v := by
  unfold Molecule.deg Molecule.degIn
  apply Finset.card_bij (fun x _hx => x.1)
  · intro x hx
    have ha := (mem_dartsAt (induced M S) v x).mp hx
    exact Finset.mem_filter.mpr ⟨(mem_dartsAt M v x.1).mpr ha,x.2⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro y hy
    obtain ⟨hyv,hyg⟩ := Finset.mem_filter.mp hy
    refine ⟨⟨y,hyg⟩,(mem_dartsAt (induced M S) v _).mpr ?_,rfl⟩
    exact (mem_dartsAt M v y).mp hyv

/-- The bond multiset of an atomic group is exactly the induced bond count. -/
theorem induced_card_bonds (S : Finset V) : (induced M S).bonds.card = (M.groupBonds S).card := by
  rw [Molecule.groupBonds,Multiset.card_map]
  change (induced M S).bonds.card = (Finset.univ.filter (fun x : D => M.out x = true ∧ M.InGroup S x)).card
  apply Finset.card_bij (fun x _hx => x.1)
  · intro x hx
    have hout := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hout,x.2⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro y hy
    have hh := (Finset.mem_filter.mp hy).2
    refine ⟨⟨y,hh.2⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1⟩

/-- Handshaking for the actual atomic group, with loops counted twice. -/
theorem sum_degreesIn_eq_two_mul_groupBonds (S : Finset V) :
    ∑ v ∈ S, M.degIn S v = 2*(M.groupBonds S).card := by
  have hh := sum_degrees_eq_two_mul_bonds (induced M S)
  simp_rw [induced_deg] at hh
  rw [induced_card_bonds] at hh
  exact hh

theorem degIn_le_deg (S : Finset V) (v : V) : M.degIn S v ≤ M.deg v :=
  Finset.card_filter_le _ _

/-- Splitting internal degree by orientation retains all half-edges. -/
theorem outIn_add_inIn (S : Finset V) (v : V) : M.outIn S v+M.inIn S v = M.degIn S v := by
  have hh := ((M.dartsAt v).filter (M.InGroup S)).card_filter_add_card_filter_not
    (fun x => M.out x = true)
  simpa only [Molecule.outIn,Molecule.inIn,Molecule.degIn,Finset.filter_filter,Bool.not_eq_true] using hh

/-- TARGET `defblock`: each of the two joints has internal degree two. -/
theorem block_joint_degrees {S : Finset V} {j1 j2 : V} (hB : M.IsBlock S j1 j2) :
    M.degIn S j1 = 2 ∧ M.degIn S j2 = 2 := by
  obtain ⟨_hS,_hj1,_hj2,_hne,ho1,hi1,ho2,hi2,_hint⟩ := hB
  have h1 := outIn_add_inIn M S j1
  have h2 := outIn_add_inIn M S j2
  omega

end WaveTurbulence.Mole
