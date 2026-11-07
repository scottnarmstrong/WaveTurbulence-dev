/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentStatistics
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwo
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
import Mathlib.Tactic

/-! # Simple degree-two atoms restrict exactly to closed component sides -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem simpleDegreeTwo_closed_side_iff (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {a : V} (ha : a ∈ S) : SimpleDegreeTwo (appbSideMolecule M S hS) a ↔ SimpleDegreeTwo M a := by
  constructor
  · rintro ⟨hd,b,hb,c,hc,hab,hac,hbc,h1,h2⟩
    exact ⟨(degree_closed_side M S hS ha).symm.trans hd,b,hS.subset_atoms hb,c,hS.subset_atoms hc,
      hab,hac,hbc,(bondsBetween_closed_side M S hS ha hb).symm.trans h1,
      (bondsBetween_closed_side M S hS ha hc).symm.trans h2⟩
  · rintro ⟨hd,b,hb,c,hc,hab,hac,hbc,h1,h2⟩
    have hbS : b ∈ S := (hS.path_mem_iff (Relation.EqvGen.rel _ _
      (Degen.adj_of_bondsBetween_pos M hab (by rw [h1]; decide)))).mp ha
    have hcS : c ∈ S := (hS.path_mem_iff (Relation.EqvGen.rel _ _
      (Degen.adj_of_bondsBetween_pos M hac (by rw [h2]; decide)))).mp ha
    exact ⟨(degree_closed_side M S hS ha).trans hd,b,hbS,c,hcS,hab,hac,hbc,
      (bondsBetween_closed_side M S hS ha hbS).trans h1,(bondsBetween_closed_side M S hS ha hcS).trans h2⟩

open Classical in
theorem simpleDegreeTwoAtoms_closed_side_filter (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    simpleDegreeTwoAtoms (appbSideMolecule M S hS) = S.filter (SimpleDegreeTwo M) := by
  classical
  ext a
  simp only [simpleDegreeTwoAtoms,mem_filter]
  constructor
  · rintro ⟨ha,hd⟩
    exact ⟨ha,(simpleDegreeTwo_closed_side_iff M S hS ha).mp hd⟩
  · rintro ⟨ha,hd⟩
    exact ⟨ha,(simpleDegreeTwo_closed_side_iff M S hS ha).mpr hd⟩

theorem simpleDegreeTwoAtoms_card_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    (simpleDegreeTwoAtoms M).card = (simpleDegreeTwoAtoms (appbSideMolecule M S hS)).card+
      (simpleDegreeTwoAtoms (appbSideMolecule M (M.atoms \ S) hS.complement)).card := by
  classical
  rw [simpleDegreeTwoAtoms_closed_side_filter,simpleDegreeTwoAtoms_closed_side_filter]
  exact filter_card_closed_partition M S hS (SimpleDegreeTwo M)

end WaveTurbulence.Mole.AppbAlgorithm
