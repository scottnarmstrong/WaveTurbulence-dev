/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBClosedSidePaths
public import WaveTurbulence.Foundations.Molecule.Degen.ComponentQuotient
import Mathlib.Tactic

/-! # The declared component quotient splits over actual closed sides -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem closed_side_path_to_old (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {a b : V} (hp : (appbSideMolecule M S hS).SameComponent a b) : M.SameComponent a b := by
  induction hp with
  | rel a b h => obtain ⟨x,hx,hy⟩ := h; exact Relation.EqvGen.rel _ _ ⟨x.val,hx,hy⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hp ih => exact ih.symm
  | trans a b c hp hp' ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

theorem old_path_to_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {a b : V} (hp : M.SameComponent a b) (ha : a ∈ S) :
    (appbSideMolecule M S hS).SameComponent a b := by
  induction hp with
  | rel a b h =>
    obtain ⟨x,hx,hy⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨⟨x,hx.symm ▸ ha⟩,hx,hy⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hp ih => exact (ih ((hS.path_mem_iff hp).mpr ha)).symm
  | trans a b c hp hp' ih ih' =>
    exact Relation.EqvGen.trans _ _ _ (ih ha) (ih' ((hS.path_mem_iff hp).mp ha))

theorem componentSet_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {a : V} (ha : a ∈ S) : componentSet (appbSideMolecule M S hS) a = componentSet M a := by
  ext b
  simp only [mem_componentSet]
  constructor
  · rintro ⟨hb,hp⟩
    exact ⟨hS.subset_atoms hb,closed_side_path_to_old M S hS hp⟩
  · rintro ⟨hb,hp⟩
    exact ⟨(hS.path_mem_iff hp).mp ha,old_path_to_closed_side M S hS hp ha⟩

theorem componentSets_closed_side_union (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    componentSets M = componentSets (appbSideMolecule M S hS) ∪
      componentSets (appbSideMolecule M (M.atoms \ S) hS.complement) := by
  classical
  ext T
  constructor
  · intro hT
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hT
    by_cases hs : a ∈ S
    · exact mem_union_left _ (mem_image.mpr ⟨a,hs,componentSet_closed_side M S hS hs⟩)
    · have hc := mem_sdiff.mpr ⟨ha,hs⟩
      exact mem_union_right _ (mem_image.mpr ⟨a,hc,componentSet_closed_side M _ hS.complement hc⟩)
  · intro hT
    rcases mem_union.mp hT with hT | hT
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp hT
      rw [componentSet_closed_side M S hS ha]
      exact mem_image.mpr ⟨a,hS.subset_atoms ha,rfl⟩
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp hT
      rw [componentSet_closed_side M _ hS.complement ha]
      exact mem_image.mpr ⟨a,(mem_sdiff.mp ha).1,rfl⟩

theorem componentSets_closed_side_disjoint (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    Disjoint (componentSets (appbSideMolecule M S hS))
      (componentSets (appbSideMolecule M (M.atoms \ S) hS.complement)) := by
  classical
  apply disjoint_left.mpr
  intro T hT hT'
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hT
  obtain ⟨b,hb,he⟩ := mem_image.mp hT'
  have ham : a ∈ componentSet (appbSideMolecule M S hS) a :=
    (mem_componentSet _ _ _).mpr ⟨ha,Relation.EqvGen.refl _⟩
  rw [← he] at ham
  exact (mem_sdiff.mp ((mem_componentSet _ _ _).mp ham).1).2 ha

theorem numComponents_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    M.numComponents = (appbSideMolecule M S hS).numComponents+
      (appbSideMolecule M (M.atoms \ S) hS.complement).numComponents := by
  rw [numComponents_eq_card_componentSets,numComponents_eq_card_componentSets,
    numComponents_eq_card_componentSets,componentSets_closed_side_union M S hS,
    card_union_of_disjoint (componentSets_closed_side_disjoint M S hS)]

end WaveTurbulence.Mole.AppbAlgorithm
