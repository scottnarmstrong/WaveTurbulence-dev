/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.LadderCover
public import WaveTurbulence.Foundations.FinalCount.AppBLinkParents
import Mathlib.Tactic

/-! # A local integer potential equivalent to the source ladder complexity -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def linkPotential (M : Molecule V D) : ℤ :=
  (M.atoms.card : ℤ)-2*(appbLinks M).card

theorem links_card_eq_sum_ladder_lengths (M : Molecule V D) (hM : M.IsMolecule) :
    (appbLinks M).card = ∑ T ∈ Degen.sourceMaximalLadders M,Molecule.ladderLength T := by
  classical
  calc
    _ = ∑ S ∈ appbLinks M,(1 : ℕ) := by simp
    _ = ∑ T ∈ Degen.sourceMaximalLadders M,
        ∑ S ∈ (appbLinks M).filter (fun S => appbLinkParent M S = T),(1 : ℕ) :=
      (sum_fiberwise_of_maps_to' (s := appbLinks M) (t := Degen.sourceMaximalLadders M)
        (fun S hS => (appbLinkParent_spec ((mem_appbLinks M S).mp hS)).1) (fun _ => (1 : ℕ))).symm
    _ = _ := by
      apply sum_congr rfl
      intro T hT
      simp only [sum_const,nsmul_eq_mul,mul_one,Nat.cast_id,appbLinkParent_fiber_card hM hT]

theorem maximal_ladder_card_eq (M : Molecule V D) {T : Finset V}
    (hT : T ∈ Degen.sourceMaximalLadders M) : T.card = 2*(Molecule.ladderLength T+1) := by
  classical
  obtain ⟨m,u,v,hL,rfl⟩ := (mem_filter.mp hT).2.1
  have hh := Degen.ladderAtoms_card_of_injective hL.2.1
  unfold Molecule.ladderLength
  rw [hh]
  have hm := hL.1
  omega

theorem linkPotential_eq_free_add_two_ladders (M : Molecule V D) (hM : M.IsMolecule) :
    linkPotential M = (sourceFreeAtoms M).card+2*((Degen.sourceMaximalLadders M).card : ℤ) := by
  classical
  let F := Degen.sourceMaximalLadders M
  have hsub : F.biUnion id ⊆ M.atoms := by
    intro a ha
    obtain ⟨T,hT,haT⟩ := mem_biUnion.mp ha
    exact Degen.sourceLadderSet_atoms_subset M (mem_filter.mp hT).2.1 haT
  have hpart : (sourceFreeAtoms M).card+(F.biUnion id).card = M.atoms.card :=
    card_sdiff_add_card_eq_card hsub
  have hsum : (F.biUnion id).card = 2*((appbLinks M).card+F.card) := by
    rw [card_biUnion (Degen.sourceMaximalLadders_pairwiseDisjoint M hM)]
    calc
      _ = ∑ T ∈ F,2*(Molecule.ladderLength T+1) := by
        apply sum_congr rfl
        intro T hT
        exact maximal_ladder_card_eq M hT
      _ = 2*((∑ T ∈ F,Molecule.ladderLength T)+F.card) := by
        simp only [mul_add,mul_one,sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,mul_sum]
        ring
      _ = _ := by rw [← links_card_eq_sum_ladder_lengths M hM]
  unfold linkPotential
  change (M.atoms.card : ℤ)-2*(appbLinks M).card = (sourceFreeAtoms M).card+2*(F.card : ℤ)
  omega

theorem sourceRho_le_linkPotential (M : Molecule V D) (hM : M.IsMolecule) :
    (sourceRho M : ℤ) ≤ linkPotential M ∧ linkPotential M ≤ 2*(sourceRho M : ℤ) := by
  rw [linkPotential_eq_free_add_two_ladders M hM]
  unfold sourceRho
  push_cast
  omega

end WaveTurbulence.Mole.AppbAlgorithm
