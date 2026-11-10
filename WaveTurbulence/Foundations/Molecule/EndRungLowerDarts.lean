/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.EndRungData

/-! # The two actual internal darts at the lower type-II joint

TARGET molecpl (2). The joint degree forces the two rail incidences to
exhaust its internal darts; no local parent relation is assumed.
-/

public section
namespace WaveTurbulence.Molecpl
open Finset Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The two incoming rung incidences exhaust the lower joint's internal darts. -/
theorem EndRungData.lower_darts {M : Molecule V D}
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) (R : EndRungData M S a b) :
    (M.dartsAt b).filter (M.InGroup S) =
      {M.mate (R.left_row.dart 2), M.mate (R.right_row.dart 2)} := by
  have hl : M.atom (M.mate (R.left_row.dart 2)) = b := R.left_row.neighbor_eq 2
  have hr : M.atom (M.mate (R.right_row.dart 2)) = b := R.right_row.neighbor_eq 2
  have hln : M.atom (M.mate (M.mate (R.left_row.dart 2))) = R.left := by
    rw [M.mate_mate]; exact R.left_row.atom_eq 2
  have hrn : M.atom (M.mate (M.mate (R.right_row.dart 2))) = R.right := by
    rw [M.mate_mate]; exact R.right_row.atom_eq 2
  have hne : M.mate (R.left_row.dart 2) ≠ M.mate (R.right_row.dart 2) := by
    intro he
    have hh := congrArg M.atom (Mole.mate_injective M he)
    exact R.distinct ((R.left_row.atom_eq 2).symm.trans (hh.trans (R.right_row.atom_eq 2)))
  have hs : {M.mate (R.left_row.dart 2),M.mate (R.right_row.dart 2)} ⊆
      (M.dartsAt b).filter (M.InGroup S) := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_filter.mpr ⟨(Mole.mem_dartsAt M b _).mpr hl,by
        change M.atom _ ∈ S ∧ M.atom (M.mate _) ∈ S
        rw [hl,hln]; exact ⟨hB.2.2.1,R.left_mem⟩⟩
    · have he := mem_singleton.mp hx
      subst x
      exact mem_filter.mpr ⟨(Mole.mem_dartsAt M b _).mpr hr,by
        change M.atom _ ∈ S ∧ M.atom (M.mate _) ∈ S
        rw [hr,hrn]; exact ⟨hB.2.2.1,R.right_mem⟩⟩
  apply (Finset.eq_of_subset_of_card_le hs ?_).symm
  have hd := (Mole.block_joint_degrees M hB).2
  change ((M.dartsAt b).filter (M.InGroup S)).card = 2 at hd
  simp [hd,hne]

omit [DecidableEq D] in
/-- For selected distinct atoms, counting their bonds can be restricted to internal darts. -/
theorem bondsBetween_eq_internal_card {M : Molecule V D} {S : Finset V}
    {c d : V} (hc : c ∈ S) (hd : d ∈ S) (hne : c ≠ d) :
    M.bondsBetween c d = (((M.dartsAt c).filter (M.InGroup S)).filter
      (fun x => M.atom (M.mate x) = d)).card := by
  rw [Mole.bondsBetween_eq_card_darts M hne]
  congr 1
  ext x
  simp only [mem_filter]
  constructor
  · rintro ⟨hx,he⟩
    exact ⟨⟨hx,⟨(Mole.mem_dartsAt M c x).mp hx ▸ hc,he ▸ hd⟩⟩,he⟩
  · rintro ⟨⟨hx,_⟩,he⟩
    exact ⟨hx,he⟩

/-- Each rung atom is joined to the lower joint by one bond, exactly as in TARGET. -/
theorem EndRungData.lower_single_counts {M : Molecule V D}
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b) (R : EndRungData M S a b) :
    M.bondsBetween b R.left = 1 ∧ M.bondsBetween b R.right = 1 := by
  have hl : M.atom (M.mate (M.mate (R.left_row.dart 2))) = R.left := by
    rw [M.mate_mate]; exact R.left_row.atom_eq 2
  have hr : M.atom (M.mate (M.mate (R.right_row.dart 2))) = R.right := by
    rw [M.mate_mate]; exact R.right_row.atom_eq 2
  constructor
  · rw [bondsBetween_eq_internal_card hB.2.2.1 R.left_mem R.left_ne_lower.symm,
      R.lower_darts hB]
    simp [Finset.filter_insert,Finset.filter_singleton,hl,hr,R.distinct.symm]
  · rw [bondsBetween_eq_internal_card hB.2.2.1 R.right_mem R.right_ne_lower.symm,
      R.lower_darts hB]
    simp [Finset.filter_insert,Finset.filter_singleton,hl,hr,R.distinct]

end WaveTurbulence.Molecpl
