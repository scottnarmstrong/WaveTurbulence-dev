/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedPotentialDifference
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GlobalNuEffects
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalSimpleDegreeTwo
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NewSpecialDeletion
public import WaveTurbulence.Foundations.FinalCount.Algorithm.R3SpecialComponent
public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33GlobalStatistics
public import WaveTurbulence.Foundations.FinalCount.AppBNormalEffects
import Mathlib.Tactic

/-! # Positive scalar-resource increments in normal S33 and R3 steps -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem s33_normal_balanced_gain (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.s33.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e)
    (hsep : ¬r.post.SameComponent (r.vertex 3) (r.vertex 4))
    (hb : ∀ a ∈ AppbPatternKind.s33.pattern.vertices,a ∉ AppbPatternKind.s33.pattern.removed →
      M.deg (r.vertex a) = 4) :
    2 ≤ balancedPotential r.post-balancedPotential M := by
  have hs := s33_normal_global_statistics M r hbridge hsep
    (hb 3 (by decide) (by decide)) (hb 4 (by decide) (by decide))
    (hb 5 (by decide) (by decide)) (hb 6 (by decide) (by decide))
  have hnu := hs.1
  have h3 := hs.2
  have h2 := normal_simpleDegreeTwo_unchanged M .s33 (by simp) r hb
  have hS := SpecialDeletion.count_le_old_add_displayed r hM
  have hcard : AppbPatternKind.s33.pattern.vertices.card = 6 := by decide
  rw [hcard] at hS
  have hSz : ((appbSpecialBonds r.post).card : ℤ) ≤ (appbSpecialBonds M).card+24 := by exact_mod_cast hS
  have h2z : ((simpleDegreeTwoAtoms r.post).card : ℤ)-(simpleDegreeTwoAtoms M).card = 0 := by
    rw [h2]; ring
  rw [balancedPotential_difference]
  omega

/-- Source 3R-1N is chosen only when its actual post component has no
special bond. This graph predicate makes the scalar increment positive. -/
theorem r3_normal_balanced_gain (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e)
    (hb : ∀ a ∈ AppbPatternKind.r3.pattern.vertices,a ∉ AppbPatternKind.r3.pattern.removed →
      M.deg (r.vertex a) = 4)
    (hn : ∀ x : Degen.RetainedDart M r.removedAtoms,
      M.SameComponent (r.vertex 1) (M.atom x.val) → ¬AppbSpecial r.post x) :
    2 ≤ balancedPotential r.post-balancedPotential M := by
  classical
  have hs := r3_normal_global_statistics M r hbridge
    (hb 2 (by decide) (by decide)) (hb 3 (by decide) (by decide)) (hb 4 (by decide) (by decide))
  have hnu := hs.1
  have h3 := hs.2
  have h2 := normal_simpleDegreeTwo_unchanged M .r3 (by simp) r hb
  have hS := r3_special_count_le_of_component_test M r hn
  have hSz : ((appbSpecialBonds r.post).card : ℤ) ≤ (appbSpecialBonds M).card := by exact_mod_cast hS
  have h2z : ((simpleDegreeTwoAtoms r.post).card : ℤ)-(simpleDegreeTwoAtoms M).card = 0 := by
    rw [h2]; ring
  rw [balancedPotential_difference]
  omega

end WaveTurbulence.Mole.AppbAlgorithm
