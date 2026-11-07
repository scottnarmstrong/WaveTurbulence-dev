/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedPotentialDifference
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionNuBound
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeCountBounds
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SimpleDegreeTwoChange
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NewSpecialDeletion
import Mathlib.Tactic

/-! # Uniform scalar-resource cost of actual controlled deletion operations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every cost is proved from old incidence data, degree caps and literal
component quotients. No statistic increment is an input. -/
theorem deletion_balanced_drop_le (M : Molecule V D) (hM : M.IsMolecule)
    {P : AppbPattern} (r : AppbRealization M P) :
    balancedPotential M-(120*(P.vertices.card : ℤ)+1616*P.removed.card) ≤ balancedPotential r.post := by
  have hnu := (abs_le.mp (realization_nu_change_abs_le M hM r)).2
  have h3 := (abs_le.mp (deletion_degreeCount_change_abs_le r 3)).1
  have h2 := (abs_le.mp (SimpleStarChange.abs_difference_le r)).1
  have hS := SpecialDeletion.count_le_old_add_displayed r hM
  have hSz : ((appbSpecialBonds r.post).card : ℤ) ≤ (appbSpecialBonds M).card+4*P.vertices.card := by exact_mod_cast hS
  have hΔ := balancedPotential_difference M r.post
  have hnon : (0 : ℤ) ≤ P.removed.card := by omega
  omega

theorem controlled_pattern_size_bounds (k : AppbPatternKind) :
    k.pattern.vertices.card ≤ 6 ∧ k.pattern.removed.card ≤ 4 := by
  cases k <;> decide

theorem pattern_deletion_balanced_drop_le (M : Molecule V D) (hM : M.IsMolecule)
    (k : AppbPatternKind) (r : AppbRealization M k.pattern) :
    balancedPotential M-8000 ≤ balancedPotential r.post := by
  have hh := deletion_balanced_drop_le M hM r
  have hs := controlled_pattern_size_bounds k
  omega

theorem common_deletion_balanced_drop_le (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M appbR23Common) :
    balancedPotential M-8000 ≤ balancedPotential r.post := by
  have hh := deletion_balanced_drop_le M hM r
  have hv : appbR23Common.vertices.card = 4 := by decide
  have hr : appbR23Common.removed.card = 3 := by decide
  rw [hv,hr] at hh
  omega

end WaveTurbulence.Mole.AppbAlgorithm
