/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SpecialCountBound
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwo
public import WaveTurbulence.Foundations.FinalCount.Algorithm.Terminal
import Mathlib.Tactic

/-! # A scalar resource for the source normal-operation balances

Only its actual initial sign is established here. Positive increments for
source-selected operations require the independent local statistic proofs.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A fixed scalar combination of actual source graph statistics. -/
noncomputable def balancedPotential (M : Molecule V D) : ℤ :=
  100*(((appbDegreeAtoms M 3).card : ℤ)-appbNu M)+appbNu M+
    4*(((simpleDegreeTwoAtoms M).card : ℤ)-(appbSpecialBonds M).card)

/-- The source initial nu<=0 condition makes this resource nonnegative.
No event-count inequality is an input. -/
theorem balancedPotential_nonneg_initial (M : Molecule V D) (hM : M.IsMolecule)
    (hnu : appbNu M ≤ 0) : 0 ≤ balancedPotential M := by
  have hs := special_count_le_two_degreeThree M hM
  have hsz : ((appbSpecialBonds M).card : ℤ) ≤ 2*(appbDegreeAtoms M 3).card := by exact_mod_cast hs
  have h3 : (0 : ℤ) ≤ (appbDegreeAtoms M 3).card := by omega
  have h2 : (0 : ℤ) ≤ (simpleDegreeTwoAtoms M).card := by omega
  unfold balancedPotential
  omega

/-- All four actual statistics vanish on the terminal isolated-atom graph. -/
theorem balancedPotential_zero_terminal (M : Molecule V D) (h : M.bonds = ∅) :
    balancedPotential M = 0 := by
  classical
  have h3 : appbDegreeAtoms M 3 = ∅ := by
    ext a
    simp only [appbDegreeAtoms,Finset.mem_filter,degree_zero_of_no_bonds M h,
      Nat.reduceEqDiff,and_false,Finset.notMem_empty]
  have h2 : simpleDegreeTwoAtoms M = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hh := (Finset.mem_filter.mp ha).2.1
    rw [degree_zero_of_no_bonds M h] at hh
    omega
  have hs : appbSpecialBonds M = ∅ := by
    letI := isEmpty_darts_of_no_bonds M h
    exact Finset.eq_empty_of_isEmpty _
  have hnu : appbNu M = 0 := by
    unfold appbNu
    rw [h,Finset.card_empty,components_eq_atoms_of_no_bonds M h]
    push_cast
    ring
  unfold balancedPotential
  rw [h3,h2,hs,hnu]
  norm_num

end WaveTurbulence.Mole.AppbAlgorithm
