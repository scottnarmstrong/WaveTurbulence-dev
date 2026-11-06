/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeOrientationGroups
public import WaveTurbulence.Foundations.Molecule.MoleculeGroupIdentities
import Mathlib.Tactic

/-! # Oriented incidence identities for unions and full-degree atoms -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

theorem orientedIn_union_add_inter (A B : Finset V) (b : Bool) {v : V} (hA : v ∈ A) (hB : v ∈ B) :
    ((M.dartsAt v).filter (fun x => M.InGroup (A ∪ B) x ∧ M.out x = b)).card +
      ((M.dartsAt v).filter (fun x => M.InGroup (A ∩ B) x ∧ M.out x = b)).card =
    ((M.dartsAt v).filter (fun x => M.InGroup A x ∧ M.out x = b)).card +
      ((M.dartsAt v).filter (fun x => M.InGroup B x ∧ M.out x = b)).card := by
  classical
  let DA := (M.dartsAt v).filter (fun x => M.InGroup A x ∧ M.out x = b)
  let DB := (M.dartsAt v).filter (fun x => M.InGroup B x ∧ M.out x = b)
  have hu : (M.dartsAt v).filter (fun x => M.InGroup (A ∪ B) x ∧ M.out x = b) = DA ∪ DB := by
    ext x
    dsimp only [DA,DB]
    simp only [Finset.mem_union,Finset.mem_filter,mem_dartsAt]
    simp only [Molecule.InGroup,Finset.mem_union]
    by_cases hx : M.atom x = v
    · simp only [hx,hA,hB,true_and,true_or]
      tauto
    · simp [hx]
  have hi : (M.dartsAt v).filter (fun x => M.InGroup (A ∩ B) x ∧ M.out x = b) = DA ∩ DB := by
    ext x
    dsimp only [DA,DB]
    simp only [Finset.mem_inter,Finset.mem_filter,mem_dartsAt]
    simp only [Molecule.InGroup,Finset.mem_inter]
    tauto
  rw [hu,hi]
  exact Finset.card_union_add_card_inter DA DB

theorem outIn_union_add_inter (A B : Finset V) {v : V} (hA : v ∈ A) (hB : v ∈ B) :
    M.outIn (A ∪ B) v+M.outIn (A ∩ B) v = M.outIn A v+M.outIn B v :=
  orientedIn_union_add_inter M A B true hA hB

theorem inIn_union_add_inter (A B : Finset V) {v : V} (hA : v ∈ A) (hB : v ∈ B) :
    M.inIn (A ∪ B) v+M.inIn (A ∩ B) v = M.inIn A v+M.inIn B v :=
  orientedIn_union_add_inter M A B false hA hB

theorem outIn_le_outdeg (S : Finset V) (v : V) : M.outIn S v ≤ M.outdeg v := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxv,_hxg,hxo⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxv,hxo⟩

theorem inIn_le_indeg (S : Finset V) (v : V) : M.inIn S v ≤ M.indeg v := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxv,_hxg,hxo⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxv,hxo⟩

/-- A full internal atom has exactly two incidences of each orientation. -/
theorem full_oriented_counts (hM : M.IsMolecule) {S : Finset V} {v : V}
    (hv : v ∈ M.atoms) (hd : M.degIn S v = 4) : M.outIn S v = 2 ∧ M.inIn S v = 2 := by
  have ho := (outIn_le_outdeg M S v).trans (hM.1 v hv).1
  have hi := (inIn_le_indeg M S v).trans (hM.1 v hv).2
  have hs := outIn_add_inIn M S v
  omega

end WaveTurbulence.Mole
