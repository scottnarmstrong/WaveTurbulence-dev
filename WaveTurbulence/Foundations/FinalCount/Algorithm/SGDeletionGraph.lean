/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionDartEquiv
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionNuBound
public import WaveTurbulence.Foundations.FinalCount.MoleProp.GeneralCircuitDeletion
public import WaveTurbulence.Foundations.FinalCount.Degen.CommonParameters
import Mathlib.Tactic

/-! # Graph bookkeeping for deleting a small set of atoms

Deleting a set `Y` of atoms of a molecule never raises the circuit rank, removes at most
`8 |Y|` bonds, and creates at most `4 |Y|` new atoms of degree other than four.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
open WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem circuitRank_erase_erase_eq_union (M : Molecule V D) (Y Z : Finset V) :
    (eraseAtoms (eraseAtoms M Y) Z).circuitRank = (eraseAtoms M (Y ∪ Z)).circuitRank := by
  refine (numComponents_and_circuitRank_eq_of_dart_equiv _ _ (eraseDartUnionEquiv M Y Z) ?_ ?_ ?_ ?_).2
  · ext a
    change (a ∈ (M.atoms \ Y) \ Z) ↔ a ∈ M.atoms \ (Y ∪ Z)
    simp only [mem_sdiff,mem_union,not_or]
    tauto
  · intro x; rfl
  · intro x; exact Subtype.ext rfl
  · intro x; rfl

theorem circuitRank_eraseAtoms_le (M : Molecule V D) (Y : Finset V) (hY : Y ⊆ M.atoms) :
    (eraseAtoms M Y).circuitRank ≤ M.circuitRank := by
  induction Y using Finset.induction_on with
  | empty =>
    have h := numComponents_and_circuitRank_eq_of_dart_equiv (eraseAtoms M ∅) M
      (eraseEmptyDartEquiv M) (by simp [eraseAtoms]) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    exact h.2.le
  | insert a Y ha ih =>
    have hsub : Y ⊆ M.atoms := fun v hv => hY (mem_insert_of_mem hv)
    have haM : a ∈ M.atoms := hY (mem_insert_self _ _)
    have haPost : a ∈ (eraseAtoms M Y).atoms := mem_sdiff.mpr ⟨haM,ha⟩
    have h1 := WaveTurbulence.MoleProp.circuitRank_erase_singleton_le_general (eraseAtoms M Y) haPost
    have hU : Y ∪ {a} = insert a Y := by
      ext v; simp only [mem_union,mem_singleton,mem_insert]; tauto
    have h2 := circuitRank_erase_erase_eq_union M Y {a}
    rw [hU] at h2
    rw [← h2]
    exact h1.trans (ih hsub)

/-- All darts at the atoms of `Y`. -/
def dartsAtSet (M : Molecule V D) (Y : Finset V) : Finset D := Y.biUnion M.dartsAt

theorem card_dartsAtSet_le (M : Molecule V D) (hM : M.IsMolecule) (Y : Finset V)
    (hY : Y ⊆ M.atoms) : (dartsAtSet M Y).card ≤ 4*Y.card := by
  calc (dartsAtSet M Y).card ≤ ∑ v ∈ Y,(M.dartsAt v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ Y,4 := sum_le_sum fun v hv => deg_le_four M hM (hY hv)
    _ = 4*Y.card := by simp [mul_comm]

theorem card_removedBonds_le (M : Molecule V D) (hM : M.IsMolecule) (Y : Finset V)
    (hY : Y ⊆ M.atoms) : (appbRemovedBonds M Y).card ≤ 8*Y.card := by
  have hsub : appbRemovedBonds M Y ⊆ dartsAtSet M Y ∪ (dartsAtSet M Y).image M.mate := by
    intro x hx
    obtain ⟨-,h⟩ := mem_filter.mp hx
    rcases h with h | h
    · exact mem_union_left _ (mem_biUnion.mpr ⟨_,h,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩)
    · refine mem_union_right _ (mem_image.mpr ⟨M.mate x,
        mem_biUnion.mpr ⟨_,h,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩,M.mate_mate x⟩)
  have h4 := card_dartsAtSet_le M hM Y hY
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (dartsAtSet M Y).card+((dartsAtSet M Y).image M.mate).card := card_union_le _ _
    _ ≤ (dartsAtSet M Y).card+(dartsAtSet M Y).card := by
        exact Nat.add_le_add_left card_image_le _
    _ ≤ 8*Y.card := by omega

theorem card_nonFour_eraseAtoms_le (M : Molecule V D) (hM : M.IsMolecule) (Y : Finset V)
    (hY : Y ⊆ M.atoms) :
    ((eraseAtoms M Y).atoms.filter (fun a => (eraseAtoms M Y).deg a ≠ 4)).card ≤
      (M.atoms.filter (fun a => M.deg a ≠ 4)).card+4*Y.card := by
  let R : Finset V := ((dartsAtSet M Y).image M.mate).image M.atom
  have hR : R.card ≤ 4*Y.card :=
    (card_image_le.trans card_image_le).trans (card_dartsAtSet_le M hM Y hY)
  have hsub : (eraseAtoms M Y).atoms.filter (fun a => (eraseAtoms M Y).deg a ≠ 4) ⊆
      M.atoms.filter (fun a => M.deg a ≠ 4) ∪ R := by
    intro z hz
    obtain ⟨hz1,hz2⟩ := mem_filter.mp hz
    have hzY := (mem_sdiff.mp hz1)
    have hdeg := deg_eraseAtoms_add_removed M Y hzY.2
    by_cases h4 : M.deg z = 4
    · apply mem_union_right
      have hne : (removedDartsAt M Y z).Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro he
        rw [he] at hdeg
        simp only [card_empty,add_zero] at hdeg
        exact hz2 (hdeg.trans h4)
      obtain ⟨x,hx⟩ := hne
      obtain ⟨hx1,hx2⟩ := mem_filter.mp hx
      refine mem_image.mpr ⟨x,mem_image.mpr ⟨M.mate x,
        mem_biUnion.mpr ⟨_,hx2,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩,M.mate_mate x⟩,?_⟩
      exact (mem_filter.mp hx1).2
    · exact mem_union_left _ (mem_filter.mpr ⟨hzY.1,h4⟩)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := by omega

end WaveTurbulence.Mole.AppbAlgorithm
