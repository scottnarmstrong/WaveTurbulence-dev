/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-!
# Exact half-edge cut identities

TARGET Definition `defcut` L2117–L2127 and F40: the chosen incoming and
outgoing darts stay at the original atom, and all its other darts move to
the fresh atom. This includes degree-two cuts and self-loops.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {v v2 : V} {x1 x2 : D}

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
theorem cut_fresh_ne (hd : M.IsCutData v v2 x1 x2) : v2 ≠ v := by
  intro he
  exact hd.2.1 (he.symm ▸ hd.1)

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
theorem cut_darts_ne (hd : M.IsCutData v v2 x1 x2) : x1 ≠ x2 := by
  intro he
  have h1 := hd.2.2.2.2.2.1
  have h2 := hd.2.2.2.2.2.2
  rw [he,h2] at h1
  contradiction

/-- The two selected half-edges are precisely the darts left at v1. -/
theorem cut_dartsAt_old (hd : M.IsCutData v v2 x1 x2) :
    (M.cut v v2 x1 x2).dartsAt v = {x1,x2} := by
  ext y
  rw [mem_dartsAt]
  by_cases h1 : y = x1
  · subst y
    simp [Molecule.cut,hd.2.2.1]
  by_cases h2 : y = x2
  · subst y
    simp [Molecule.cut,hd.2.2.2.1]
  by_cases hv : M.atom y = v
  · simp [Molecule.cut,hv,h1,h2,cut_fresh_ne M hd]
  · simp [Molecule.cut,hv,h1,h2]

/-- Exactly the unselected darts of the old atom move to the new one. -/
theorem cut_dartsAt_new (hd : M.IsCutData v v2 x1 x2) :
    (M.cut v v2 x1 x2).dartsAt v2 = M.dartsAt v \ {x1,x2} := by
  ext y
  rw [mem_dartsAt]
  have hnone : M.atom y ≠ v2 := fun he => hd.2.1 (he ▸ M.atom_mem y)
  by_cases h1 : y = x1
  · subst y
    simp [Molecule.cut,Finset.mem_sdiff,mem_dartsAt,hnone]
  by_cases h2 : y = x2
  · subst y
    simp [Molecule.cut,Finset.mem_sdiff,mem_dartsAt,hnone]
  by_cases hv : M.atom y = v
  · simp [Molecule.cut,Finset.mem_sdiff,mem_dartsAt,hv,h1,h2]
  · simp [Molecule.cut,Finset.mem_sdiff,mem_dartsAt,hv,h1,h2,hnone]

/-- Every unaffected atom keeps exactly its original darts. -/
theorem cut_dartsAt_other {z : V} (hz : z ≠ v) (hz2 : z ≠ v2) :
    (M.cut v v2 x1 x2).dartsAt z = M.dartsAt z := by
  ext y
  simp only [mem_dartsAt,Molecule.cut]
  split_ifs with hy
  · have h1 : v2 ≠ z := Ne.symm hz2
    have h2 : M.atom y ≠ z := by rw [hy.1]; exact Ne.symm hz
    simp only [h1,h2]
  · rfl

omit [Fintype D] in
/-- A cut creates exactly one fresh atom. -/
theorem cut_card_atoms (hd : M.IsCutData v v2 x1 x2) :
    (M.cut v v2 x1 x2).atoms.card = M.atoms.card+1 := by
  exact Finset.card_insert_of_notMem hd.2.1

/-- The actual directed bond representatives are unchanged. -/
theorem cut_bonds : (M.cut v v2 x1 x2).bonds = M.bonds := rfl

/-- The kept atom has degree two, even when the two darts form a self-loop. -/
theorem cut_deg_old (hd : M.IsCutData v v2 x1 x2) : (M.cut v v2 x1 x2).deg v = 2 := by
  rw [Molecule.deg,cut_dartsAt_old M hd]
  simp only [Finset.card_pair (cut_darts_ne M hd)]

/-- Degrees are conserved by the split. -/
theorem cut_deg_new_add_two (hd : M.IsCutData v v2 x1 x2) :
    (M.cut v v2 x1 x2).deg v2+2 = M.deg v := by
  have hsub : {x1,x2} ⊆ M.dartsAt v := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_dartsAt M v _).mpr hd.2.2.1
    · exact (mem_dartsAt M v _).mpr hd.2.2.2.1
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_pair (cut_darts_ne M hd)] at hcard
  simpa only [Molecule.deg,cut_dartsAt_new M hd] using hcard

/-- Exact circuit-rank increment in terms of the actual component increment. -/
theorem cut_circuitRank (hd : M.IsCutData v v2 x1 x2) :
    (M.cut v v2 x1 x2).circuitRank = M.circuitRank-1+
      (((M.cut v v2 x1 x2).numComponents:ℤ)-(M.numComponents:ℤ)) := by
  simp only [Molecule.circuitRank,cut_bonds,cut_card_atoms M hd,Nat.cast_add,Nat.cast_one]
  ring

end WaveTurbulence.Mole
