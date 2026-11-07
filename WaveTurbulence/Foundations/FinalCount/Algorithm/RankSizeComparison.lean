/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.InitialStatistics
import Mathlib.Tactic

/-! # Circuit rank pays exponential branching except at deficient atoms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem degreeDeficit_le_four_mul_nonFour (M : Molecule V D) :
    degreeDeficit M ≤ 4*(M.atoms.filter (fun a => M.deg a ≠ 4)).card := by
  classical
  unfold degreeDeficit
  calc
    _ ≤ ∑ a ∈ M.atoms,if M.deg a ≠ 4 then (4 : ℕ) else 0 := by
      apply sum_le_sum
      intro a ha
      by_cases hd : M.deg a = 4
      · simp only [hd,Nat.sub_self,ne_eq,not_true_eq_false,ite_false,le_refl]
      · simp only [hd,ne_eq,not_false_eq_true,ite_true]
        omega
    _ = _ := by
      rw [← sum_filter]
      simp only [sum_const,smul_eq_mul]
      omega

/-- For the source molecule, all exponential-in-size choices can be paid
by increasing C-plus in its circuit-rank normalization, with an explicit
remainder for its non-degree-four atoms. -/
theorem atoms_le_rank_add_two_mul_nonFour (M : Molecule V D) (hM : M.IsMolecule) :
    (M.atoms.card : ℤ) ≤ M.circuitRank+2*((M.atoms.filter (fun a => M.deg a ≠ 4)).card : ℤ) := by
  have hh := degree_sum_add_deficit M hM
  have hd := degreeDeficit_le_four_mul_nonFour M
  have hn : 2*M.atoms.card ≤ M.bonds.card+2*(M.atoms.filter (fun a => M.deg a ≠ 4)).card := by omega
  have hz : 2*(M.atoms.card : ℤ) ≤ (M.bonds.card : ℤ)+2*((M.atoms.filter (fun a => M.deg a ≠ 4)).card : ℤ) := by
    exact_mod_cast hn
  unfold Molecule.circuitRank
  omega

theorem atoms_le_rank_add_two_mul_of_nonFour_le (M : Molecule V D) (hM : M.IsMolecule)
    (w : ℕ) (hw : (M.atoms.filter (fun a => M.deg a ≠ 4)).card ≤ w) :
    (M.atoms.card : ℤ) ≤ M.circuitRank+2*(w : ℤ) := by
  have hh := atoms_le_rank_add_two_mul_nonFour M hM
  omega

end WaveTurbulence.Mole.AppbAlgorithm
