/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestAct
public import WaveTurbulence.Foundations.FinalCount.Algorithm.InitialStatistics
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedPotential
public import WaveTurbulence.Foundations.FinalCount.Algorithm.LadderCover
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ActivePotential
public import WaveTurbulence.Foundations.FinalCount.Algorithm.RankSizeComparison
import Mathlib.Tactic

/-! # Initial data for the third bound of DH23 Prop 10.2

For a connected molecule with at most `w` atoms of degree other than four, the balanced
potential is at least `-396 w` and the source ladder complexity is at most the actual
active-link potential plus one (DH23 L1915-L1917: initial remainders of size `C(w+1)`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem degreeDeficit_le_nonFour (M : Molecule V D) (w : ℕ)
    (hw : (M.atoms.filter (fun a => M.deg a ≠ 4)).card ≤ w) : degreeDeficit M ≤ 4*w := by
  unfold degreeDeficit
  have h1 : ∑ v ∈ M.atoms.filter (fun a => M.deg a ≠ 4),(4-M.deg v) = ∑ v ∈ M.atoms,(4-M.deg v) := by
    apply Finset.sum_filter_of_ne
    intro v _ hne h4
    simp [h4] at hne
  rw [← h1]
  calc _ ≤ ∑ _v ∈ M.atoms.filter (fun a => M.deg a ≠ 4),4 := sum_le_sum (fun v _ => Nat.sub_le _ _)
    _ = (M.atoms.filter (fun a => M.deg a ≠ 4)).card*4 := by simp
    _ ≤ w*4 := Nat.mul_le_mul_right 4 hw
    _ = 4*w := by ring

theorem sourceRho_le_active_add_one (M : Molecule V D) (hM : M.IsMolecule)
    (hc : ∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) :
    (sourceRho M : ℤ) ≤ activeLinkPotential M+1 := by
  by_cases hb : M.bonds.Nonempty
  · have := sourceRho_le_active_initial M hM hc hb
    omega
  · have hbe : M.bonds = ∅ := not_nonempty_iff_eq_empty.mp hb
    have h1 := sourceRho_le_ladder_cover M hM ∅ (by simp)
    have h2 : M.atoms.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb'
      exact eq_of_sameComponent_of_degree_zero M (hc a ha b hb') (degree_zero_of_no_bonds M hbe b)
    have h3 := activeLinkPotential_terminal M hbe
    simp only [Finset.card_empty,Finset.biUnion_empty,sdiff_empty,zero_add] at h1
    omega

end WaveTurbulence.Mole.AppbAlgorithm
