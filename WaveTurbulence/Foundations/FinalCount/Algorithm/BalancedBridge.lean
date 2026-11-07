/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedPotentialDifference
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BridgeLocalCountBounds
public import WaveTurbulence.Foundations.FinalCount.Algorithm.Bridge333SpecialCount
import Mathlib.Tactic

/-! # Every normal bridge step strictly increases the actual scalar resource -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bridge333_balanced_gain (M : Molecule V D) (hno : AppbNoLoops M)
    (e : D) (hb : Degen.IsBridge M e) (hout : M.out e = true)
    (h1 : M.deg (M.atom e) = 3) (h2 : M.deg (M.atom (M.mate e)) = 3) :
    2 ≤ balancedPotential (eraseBond M e)-balancedPotential M := by
  classical
  have hnu := appb_bridge_nu M e hb
  have h3 := appb_bridge_degreeThree M e hb
  simp only [h1,h2,ite_true,Nat.reduceEqDiff,ite_false] at h3
  have hS := bridge333_special_count M hno e hb hout h1 h2
  have h2le := bridge333_simpleDegreeTwo_nondecrease M e hb h1 h2
  have h2z : ((simpleDegreeTwoAtoms M).card : ℤ) ≤ (simpleDegreeTwoAtoms (eraseBond M e)).card := by
    exact_mod_cast h2le
  rw [balancedPotential_difference]
  by_cases hs : AppbSpecial M e
  · simp only [hs,ite_true] at hS
    have hSz : ((appbSpecialBonds (eraseBond M e)).card : ℤ)+1 = (appbSpecialBonds M).card := by
      exact_mod_cast hS
    omega
  · simp only [hs,ite_false,add_zero] at hS
    have h2ne : (simpleDegreeTwoAtoms (eraseBond M e)).card ≠ (simpleDegreeTwoAtoms M).card := by
      intro he
      exact hs ((bridge333_simpleDegreeTwo_eq_iff_special M hno e hb hout h1 h2).mp he)
    have h2strict : (simpleDegreeTwoAtoms M).card+1 ≤ (simpleDegreeTwoAtoms (eraseBond M e)).card := by omega
    have h2strictz : ((simpleDegreeTwoAtoms M).card : ℤ)+1 ≤ (simpleDegreeTwoAtoms (eraseBond M e)).card := by
      exact_mod_cast h2strict
    have hSz : ((appbSpecialBonds (eraseBond M e)).card : ℤ) = (appbSpecialBonds M).card := by exact_mod_cast hS
    omega

theorem bridge_other_balanced_gain (M : Molecule V D) (hM : M.IsMolecule)
    (e : D) (hb : Degen.IsBridge M e)
    (hother : ¬(M.deg (M.atom e) = 3 ∧ M.deg (M.atom (M.mate e)) = 3)) :
    2 ≤ balancedPotential (eraseBond M e)-balancedPotential M := by
  have hnu := appb_bridge_nu M e hb
  have h3 := appb_bridge_degreeThree_lower_eq M e hb
  have h3lo : -(1 : ℤ) ≤ ((appbDegreeAtoms (eraseBond M e) 3).card : ℤ)-(appbDegreeAtoms M 3).card := by
    have hn : ((appbDegreeAtoms (eraseBond M e) 3).card : ℤ)-(appbDegreeAtoms M 3).card ≠ -2 :=
      fun h => hother (h3.2.mp h)
    omega
  have h2 := (abs_le.mp (bridge_simple_count_change_abs_le_two M e hb)).1
  have hS := bridge_special_count_le_old_add_eight M hM e hb
  have hSz : ((appbSpecialBonds (eraseBond M e)).card : ℤ) ≤ (appbSpecialBonds M).card+8 := by exact_mod_cast hS
  rw [balancedPotential_difference]
  omega

/-- A source BR-N step, represented by an outgoing dart, pays at least two
units in the actual scalar resource, regardless of its endpoint degrees. -/
theorem bridge_balanced_gain (M : Molecule V D) (hM : M.IsMolecule) (hno : AppbNoLoops M)
    (e : D) (hb : Degen.IsBridge M e) (hout : M.out e = true) :
    2 ≤ balancedPotential (eraseBond M e)-balancedPotential M := by
  by_cases h : M.deg (M.atom e) = 3 ∧ M.deg (M.atom (M.mate e)) = 3
  · exact bridge333_balanced_gain M hno e hb hout h.1 h.2
  · exact bridge_other_balanced_gain M hM e hb h

end WaveTurbulence.Mole.AppbAlgorithm
