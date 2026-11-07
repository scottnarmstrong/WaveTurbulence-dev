/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ConsecutiveD33
public import WaveTurbulence.Foundations.FinalCount.Algorithm.BalancedPotentialDifference
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GlobalNuEffects
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalSimpleDegreeTwo
import Mathlib.Tactic

/-! # Long chains of normal D33 steps have no scalar-resource loss internally -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem consecutive_d33_balanced_nondecrease (M : Molecule V D) (hno : AppbNoLoops M)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (t : AppbRealization r.post AppbPatternKind.d33.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e)
    (hb : ∀ a ∈ AppbPatternKind.d33.pattern.vertices,a ∉ AppbPatternKind.d33.pattern.removed →
      M.deg (r.vertex a) = 4)
    (h1 : t.vertex 1 = r.vertex 3) (h2 : t.vertex 2 = r.vertex 4)
    (ht3 : r.post.deg (t.vertex 3) = 4) (ht4 : r.post.deg (t.vertex 4) = 4) :
    0 ≤ balancedPotential r.post-balancedPotential M := by
  have hs := d33_normal_global_statistics M r hbridge
    (hb 3 (by decide) (by decide)) (hb 4 (by decide) (by decide))
  have hnu := hs.1
  have h3 := hs.2
  have h2eq := normal_simpleDegreeTwo_unchanged M .d33 (by simp) r hb
  have hSz := consecutive_d33_special_count_le M hno r t h1 h2 ht3 ht4
  have hS : ((appbSpecialBonds r.post).card : ℤ) ≤ (appbSpecialBonds M).card := by exact_mod_cast hSz
  have h2z : ((simpleDegreeTwoAtoms r.post).card : ℤ)-(simpleDegreeTwoAtoms M).card = 0 := by
    rw [h2eq]; ring
  rw [balancedPotential_difference]
  omega

end WaveTurbulence.Mole.AppbAlgorithm
