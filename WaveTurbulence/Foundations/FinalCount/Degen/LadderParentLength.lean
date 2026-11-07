/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
public import WaveTurbulence.Foundations.FinalCount.WorldSelectedLadderDisjoint
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderRestriction
import Mathlib.Tactic

/-! # Actual length deficit for all surviving children of one maximal ladder -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every genuine surviving segment inside an old maximal ladder extends
to a post-removal maximal ladder which is still contained in that old parent. -/
theorem exists_sourceMaximalLadder_extension_in_parent (M : Molecule V D) (hM : M.IsMolecule)
    {z : V} {S T : Finset V} (hS : S ∈ sourceMaximalLadders M)
    (hT : SourceLadderSet (eraseAtoms M {z}) T) (hTS : T ⊆ S) :
    ∃ R ∈ sourceMaximalLadders (eraseAtoms M {z}), T ⊆ R ∧ R ⊆ S := by
  classical
  obtain ⟨R,hR,hTR⟩ := exists_sourceMaximalLadder_superset (eraseAtoms M {z}) hT
  have hRnew : SourceLadderSet (eraseAtoms M {z}) R := (mem_filter.mp hR).2.1
  have hRold : SourceLadderSet M R := ((sourceLadderSet_erase_iff M {z} R).mp hRnew).1
  obtain ⟨n,p,q,hRseq,hRatoms⟩ := hRold
  have hcard := sourceLadderSet_card_eq_length (eraseAtoms M {z}) hT
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < T.card)
  have hmeet : ∃ x, x ∈ S ∧ x ∈ Molecule.ladderAtoms p q := by
    refine ⟨x,hTS hx,?_⟩
    rw [hRatoms]
    exact hTR hx
  have hRS := sourceLadder_subset_maximal_of_intersects M
    (fun a ha => Mole.deg_le_four M hM ha) hS hRseq hmeet
  refine ⟨R,hR,hTR,?_⟩
  simpa only [hRatoms] using hRS

/-- Actual source maximal-ladder lengths lose at most two units at the
old parent containing the deleted atom, and no units at any other parent.
All post maximal extensions and all length comparisons are proved here. -/
theorem sourceMaximalLadder_parent_length_deficit (M : Molecule V D) (hM : M.IsMolecule)
    (z : V) {S : Finset V} (hS : S ∈ sourceMaximalLadders M) :
    Molecule.ladderLength S ≤
      (∑ T ∈ (sourceMaximalLadders (eraseAtoms M {z})).filter (fun T => T ⊆ S),
        Molecule.ladderLength T) + if z ∈ S then 2 else 0 := by
  classical
  let N := eraseAtoms M {z}
  let K := (sourceMaximalLadders N).filter (fun T => T ⊆ S)
  by_cases hz : z ∈ S
  · have hSsrc : SourceLadderSet M S := (mem_filter.mp hS).2.1
    obtain ⟨C,_hcard,hCsrc,hCdis,hClen⟩ := sourceLadderSet_split_after_atom_delete M hSsrc hz
    have hExt (T : Finset V) (hT : T ∈ C) : ∃ R ∈ K, T ⊆ R := by
      obtain ⟨R,hR,hTR,hRS⟩ := exists_sourceMaximalLadder_extension_in_parent M hM hS
        (hCsrc T hT).1 (hCsrc T hT).2
      exact ⟨R,mem_filter.mpr ⟨hR,hRS⟩,hTR⟩
    let f (T : Finset V) : Finset V := if h : T ∈ C then Classical.choose (hExt T h) else ∅
    have hf (T : Finset V) (hT : T ∈ C) : f T ∈ K ∧ T ⊆ f T := by
      simp only [f,dif_pos hT]
      exact Classical.choose_spec (hExt T hT)
    have hmaps : (C : Set (Finset V)).MapsTo f K := fun T hT => (hf T hT).1
    have hsum : (∑ T ∈ C, Molecule.ladderLength T) ≤ ∑ R ∈ K, Molecule.ladderLength R := by
      rw [← sum_fiberwise_of_maps_to hmaps]
      apply sum_le_sum
      intro R hR
      let F := C.filter (fun T => f T = R)
      have hFsrc : ∀ T ∈ F, SourceLadderSet N T := by
        intro T hT
        exact (hCsrc T (mem_filter.mp hT).1).1
      have hRsrc : SourceLadderSet N R := (mem_filter.mp (mem_filter.mp hR).1).2.1
      have hFdis : (F : Set (Finset V)).PairwiseDisjoint id := by
        intro A hA B hB hAB
        exact hCdis (mem_filter.mp hA).1 (mem_filter.mp hB).1 hAB
      have hFR : ∀ T ∈ F, T ⊆ R := by
        intro T hT
        obtain ⟨hTC,hfT⟩ := mem_filter.mp hT
        have hh := (hf T hTC).2
        rwa [hfT] at hh
      exact sum_ladderLength_le_of_disjoint_subsets N F R hFsrc hRsrc hFdis hFR
    have hh := hClen.trans (Nat.add_le_add_right hsum 2)
    simpa only [hz,ite_true] using hh
  · have hdis : Disjoint S {z} := disjoint_singleton_right.mpr hz
    have hSnew := sourceMaximalLadder_erase_of_disjoint M {z} hS hdis
    have hSK : S ∈ K := mem_filter.mpr ⟨hSnew,Subset.rfl⟩
    have hh : Molecule.ladderLength S ≤ ∑ R ∈ K, Molecule.ladderLength R :=
      single_le_sum (fun R _ => Nat.zero_le (Molecule.ladderLength R)) hSK
    simpa only [hz,ite_false,Nat.add_zero] using hh

end WaveTurbulence.Degen
