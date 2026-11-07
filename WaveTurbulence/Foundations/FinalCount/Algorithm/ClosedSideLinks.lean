/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideBonds
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
import Mathlib.Tactic

/-! # The actual selected-link family splits across closed component sides -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem link_closed_side_iff (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    (T : Finset V) : AppbLink (appbSideMolecule M S hS) T ↔ AppbLink M T ∧ T ⊆ S := by
  constructor
  · rintro ⟨u,v,h,rfl⟩
    obtain ⟨hL,hm⟩ := (sourceLadder_closed_side_iff M S hS u v).mp h
    refine ⟨⟨u,v,hL,rfl⟩,?_⟩
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      exact (hm i).1
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      exact (hm i).2
  · rintro ⟨⟨u,v,hL,rfl⟩,hsub⟩
    refine ⟨u,v,(sourceLadder_closed_side_iff M S hS u v).mpr ⟨hL,?_⟩,rfl⟩
    intro i
    exact ⟨hsub (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)),
      hsub (mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))⟩

/-- A length-one selected ladder has an actual path from its first rung
atom to each of its four atoms. -/
theorem link_presentation_paths (M : Molecule V D) (u v : Fin 2 → V)
    (hL : Degen.SourceLadder (m := 1) M u v) :
    ∀ a ∈ Molecule.ladderAtoms u v,M.SameComponent (u 0) a := by
  have hinj := hL.2.1
  have hn01 : u 0 ≠ u 1 := fun he => by
    have hh := hinj (show Sum.elim u v (.inl 0) = Sum.elim u v (.inl 1) from he)
    cases hh
  have hcross (i : Fin 2) : u i ≠ v i := fun he => by
    have hh := hinj (show Sum.elim u v (.inl i) = Sum.elim u v (.inr i) from he)
    cases hh
  have hrail : M.bondsBetween (u 0) (u 1) = 1 := (hL.2.2.2.2 (0 : Fin 1)).1
  have hu : M.SameComponent (u 0) (u 1) := Relation.EqvGen.rel _ _
    (Degen.adj_of_bondsBetween_pos M hn01 (by rw [hrail]; decide))
  have hv (i : Fin 2) : M.SameComponent (u i) (v i) := Relation.EqvGen.rel _ _
    (Degen.adj_of_bondsBetween_pos M (hcross i) (by rw [hL.2.2.2.1 i]; decide))
  intro a ha
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
    fin_cases i
    · exact Relation.EqvGen.refl _
    · exact hu
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
    fin_cases i
    · exact hv 0
    · exact Relation.EqvGen.trans _ _ _ hu (hv 1)

theorem link_subset_one_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {T : Finset V} (hT : AppbLink M T) : T ⊆ S ∨ T ⊆ M.atoms \ S := by
  obtain ⟨u,v,hL,rfl⟩ := hT
  by_cases h0 : u 0 ∈ S
  · exact Or.inl (fun a ha => (hS.path_mem_iff (link_presentation_paths M u v hL a ha)).mp h0)
  · refine Or.inr (fun a ha => mem_sdiff.mpr ⟨?_,?_⟩)
    · exact (Degen.sourceLadderSet_atoms_subset M ⟨1,u,v,hL,rfl⟩) ha
    · exact fun hi => h0 ((hS.path_mem_iff (link_presentation_paths M u v hL a ha)).mpr hi)

end WaveTurbulence.Mole.AppbAlgorithm
