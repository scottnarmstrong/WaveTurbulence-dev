/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideMolecule
public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
import Mathlib.Tactic

/-! # Exact restriction and additivity of actual outgoing special bonds -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem special_closed_side_iff (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    (x : AppbSideDart M S) : AppbSpecial (appbSideMolecule M S hS) x ↔ AppbSpecial M x.val := by
  have hxS := x.property
  have hyS := (hS.mate_mem x.val).mp hxS
  constructor
  · rintro ⟨ho,hd1,hd2,a,ha,b,hb,hab,ha1,ha2,hb1,hb2,hcentral,hA,hB⟩
    exact ⟨ho,(degree_closed_side M S hS hxS).symm.trans hd1,
      (degree_closed_side M S hS hyS).symm.trans hd2,a,hS.subset_atoms ha,b,hS.subset_atoms hb,
      hab,ha1,ha2,hb1,hb2,(bondsBetween_closed_side M S hS hxS hyS).symm.trans hcentral,
      (bondsBetween_closed_side M S hS hxS ha).symm.trans hA,
      (bondsBetween_closed_side M S hS hyS hb).symm.trans hB⟩
  · rintro ⟨ho,hd1,hd2,a,ha,b,hb,hab,ha1,ha2,hb1,hb2,hcentral,hA,hB⟩
    have haS := (hS.path_mem_iff (Relation.EqvGen.rel _ _
      (Degen.adj_of_bondsBetween_pos M ha1.symm (by rw [hA]; decide)))).mp hxS
    have hbS := (hS.path_mem_iff (Relation.EqvGen.rel _ _
      (Degen.adj_of_bondsBetween_pos M hb2.symm (by rw [hB]; decide)))).mp hyS
    exact ⟨ho,(degree_closed_side M S hS hxS).trans hd1,
      (degree_closed_side M S hS hyS).trans hd2,a,haS,b,hbS,hab,ha1,ha2,hb1,hb2,
      (bondsBetween_closed_side M S hS hxS hyS).trans hcentral,
      (bondsBetween_closed_side M S hS hxS haS).trans hA,
      (bondsBetween_closed_side M S hS hyS hbS).trans hB⟩

theorem specialBonds_closed_side_image (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    (appbSpecialBonds (appbSideMolecule M S hS)).image Subtype.val =
      (appbSpecialBonds M).filter (fun x => M.atom x ∈ S) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    have hs := (special_closed_side_iff M S hS y).mp (mem_filter.mp hy).2
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hs⟩,y.property⟩
  · intro hx
    obtain ⟨hx,hSx⟩ := mem_filter.mp hx
    let y : AppbSideDart M S := ⟨x,hSx⟩
    exact mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,
      (special_closed_side_iff M S hS y).mpr (mem_filter.mp hx).2⟩,rfl⟩

theorem specialBonds_card_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    (appbSpecialBonds (appbSideMolecule M S hS)).card =
      ((appbSpecialBonds M).filter (fun x => M.atom x ∈ S)).card := by
  rw [← specialBonds_closed_side_image M S hS,card_image_of_injective _ Subtype.val_injective]

theorem specialBonds_card_closed_side_add (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S) :
    (appbSpecialBonds M).card = (appbSpecialBonds (appbSideMolecule M S hS)).card+
      (appbSpecialBonds (appbSideMolecule M (M.atoms \ S) hS.complement)).card := by
  classical
  rw [specialBonds_card_closed_side,specialBonds_card_closed_side]
  have he : (appbSpecialBonds M).filter (fun x => M.atom x ∈ M.atoms \ S) =
      (appbSpecialBonds M).filter (fun x => ¬M.atom x ∈ S) := by
    ext x
    simp only [mem_filter,mem_sdiff,M.atom_mem,true_and]
  rw [he,card_filter_add_card_filter_not]

end WaveTurbulence.Mole.AppbAlgorithm
