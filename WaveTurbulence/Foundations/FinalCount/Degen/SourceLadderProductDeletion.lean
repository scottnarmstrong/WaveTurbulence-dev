/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.LadderParentLength
public import WaveTurbulence.Foundations.FinalCount.Degen.InheritedSourceScales
public import WaveTurbulence.Foundations.FinalCount.Degen.FiniteLadderProducts
import Mathlib.Tactic

/-! # Actual selected-ladder product under deletion of one atom -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Deleting one atom costs at most four logarithmic powers in the literal
source ladder product, with the inherited scale on every actual new ladder. -/
theorem sourceLadderProduct_le_log_four_mul_erase (M : Molecule V D) (hM : M.IsMolecule)
    (z : V) {L γ δ : ℝ} (hL : 0 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : 0 ≤ δ)
    (P : Finset V → ℝ) (hP : ∀ S ∈ sourceMaximalLadders M, 0 ≤ P S) :
    sourceLadderProduct M L γ δ P ≤ Real.log L ^ 4 *
      sourceLadderProduct (eraseAtoms M {z}) L γ δ (inheritedSourceScale M P) := by
  classical
  let A := sourceMaximalLadders M
  let B := sourceMaximalLadders (eraseAtoms M {z})
  have hex (T : Finset V) (hT : T ∈ B) : ∃ S, S ∈ A ∧ T ⊆ S := by
    obtain ⟨S,hS,_⟩ := existsUnique_source_parent M hM {z} hT
    exact ⟨S,hS⟩
  let parent (T : Finset V) := if h : T ∈ B then Classical.choose (hex T h) else ∅
  have hp (T : Finset V) (hT : T ∈ B) : parent T ∈ A ∧ T ⊆ parent T := by
    simp only [parent,dite_eq_left hT]
    exact Classical.choose_spec (hex T hT)
  have hparent (T S : Finset V) (hT : T ∈ B) (hS : S ∈ A) :
      parent T = S ↔ T ⊆ S := by
    constructor
    · intro he
      rw [← he]
      exact (hp T hT).2
    · intro hTS
      obtain ⟨S0,hS0,hu⟩ := existsUnique_source_parent M hM {z} hT
      exact (hu (parent T) (hp T hT)).trans (hu S ⟨hS,hTS⟩).symm
  let bad := (A.filter (fun S => z ∈ S)).biUnion id
  have hbad (S : Finset V) (hS : S ∈ A) (hz : z ∈ S) : S = bad := by
    have he : A.filter (fun T => z ∈ T) = {S} := by
      ext T
      simp only [mem_filter,mem_singleton]
      constructor
      · rintro ⟨hT,hzT⟩
        by_contra hne
        have hd := sourceMaximalLadders_pairwiseDisjoint M hM hT hS hne
        exact (disjoint_left.mp hd) hzT hz
      · rintro rfl
        exact ⟨hS,hz⟩
    change S = (A.filter (fun T => z ∈ T)).biUnion id
    rw [he]
    ext x
    simp
  let w := fun S => Molecule.ladderWeight L γ δ (P S)
  have hw (S : Finset V) (hS : S ∈ A) : 1 ≤ w S := by
    apply le_min
    · nlinarith only [hlog, sq_nonneg (Real.log L - 1)]
    · have ht := mul_nonneg (mul_nonneg hδ (Real.rpow_nonneg hL (2*γ))) (hP S hS)
      change 1 ≤ 1 + δ * L ^ (2*γ) * P S
      linarith only [ht]
  have hwQ (S : Finset V) (_hS : S ∈ A) : w S ≤ Real.log L ^ 2 := min_le_left _ _
  have hQ : 1 ≤ Real.log L ^ 2 := by nlinarith only [hlog,sq_nonneg (Real.log L - 1)]
  have hlen (S : Finset V) (hS : S ∈ A) :
      Molecule.ladderLength S ≤
        (∑ T ∈ B.filter (fun T => parent T = S), Molecule.ladderLength T) +
          if S = bad then 2 else 0 := by
    have he : B.filter (fun T => parent T = S) = B.filter (fun T => T ⊆ S) := by
      ext T
      simp only [mem_filter]
      exact and_congr_right (fun hT => hparent T S hT hS)
    rw [he]
    have hh := sourceMaximalLadder_parent_length_deficit M hM z hS
    change Molecule.ladderLength S ≤ (∑ T ∈ B.filter (fun T => T ⊆ S),
      Molecule.ladderLength T) + if z ∈ S then 2 else 0 at hh
    by_cases hz : z ∈ S
    · rw [if_pos hz] at hh
      rw [if_pos (hbad S hS hz)]
      exact hh
    · exact hh.trans (Nat.add_le_add_left (by simp only [hz,ite_false]; omega) _)
  have hh := prod_ladder_powers_le_of_one_length_loss A B parent
    (fun T hT => (hp T hT).1) w Molecule.ladderLength Molecule.ladderLength bad hQ hw hwQ hlen
  have hpost : (∏ T ∈ B, w (parent T) ^ Molecule.ladderLength T) =
      sourceLadderProduct (eraseAtoms M {z}) L γ δ (inheritedSourceScale M P) := by
    apply prod_congr rfl
    intro T hT
    have he := inheritedSourceScale_eq_parent M hM {z} P hT (hp T hT).1 (hp T hT).2
    rw [he]
  rw [hpost] at hh
  have he : (Real.log L ^ 2) ^ 2 = Real.log L ^ 4 := by ring
  rw [he] at hh
  exact hh

/-- A weak circuit-rank loss leaves the literal ladder product unchanged.
The exclusion of the removed atom from ladders follows from the proved
local rectangle geometry rather than a tameness assumption. -/
theorem sourceLadderProduct_erase_eq_of_weak_circuit_loss (M : Molecule V D)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (z : V) (hweak : M.circuitRank - 1 ≤ (eraseAtoms M {z}).circuitRank)
    (L γ δ : ℝ) (P : Finset V → ℝ) :
    sourceLadderProduct (eraseAtoms M {z}) L γ δ (inheritedSourceScale M P) =
      sourceLadderProduct M L γ δ P := by
  classical
  have havoid (S : Finset V) (hS : SourceLadderSet M S) : Disjoint S {z} := by
    apply disjoint_singleton_right.mpr
    intro hz
    have hh := circuitRank_erase_sourceLadder_atom_le_sub_two M hconn hS hz
    omega
  have hfamily := sourceMaximalLadders_erase_eq_of_all_disjoint M {z} havoid
  unfold sourceLadderProduct
  rw [hfamily]
  apply prod_congr rfl
  intro S hS
  rw [inheritedSourceScale_eq_on_old_maximal M P hS]

end WaveTurbulence.Degen
