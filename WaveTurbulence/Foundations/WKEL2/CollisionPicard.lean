/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CollisionBanach
public import WaveTurbulence.Foundations.WKEL2.CubicUniqueness
public import WaveTurbulence.Foundations.WKEL2.CubicMild

/-!
# Quantitative local well-posedness in the exact weighted L² model

The field is the unique continuous extension of the actual Schwartz collision
operator. Agreement with the frozen Schwartz solution class is handled separately.
-/

public section

noncomputable section

open Set
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance collisionNormedOp : NormedAddCommGroup
    (WeightedL2Space d →L[ℝ] WeightedL2Space d) := inferInstance
local instance collisionSpaceOp : NormedSpace ℝ
    (WeightedL2Space d →L[ℝ] WeightedL2Space d) := inferInstance
local instance collisionNormedOp₂ : NormedAddCommGroup
    (WeightedL2Space d →L[ℝ] WeightedL2Space d →L[ℝ] WeightedL2Space d) := inferInstance
local instance collisionSpaceOp₂ : NormedSpace ℝ
    (WeightedL2Space d →L[ℝ] WeightedL2Space d →L[ℝ] WeightedL2Space d) := inferInstance

/-- Quantitative local existence for every nonzero weighted L² datum. -/
theorem exists_weightedL2_mild_solution (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) {x : WeightedL2Space d} (hx : x ≠ 0) :
    ∃ u : ℝ → WeightedL2Space d, u 0 = x ∧
      IsCubicMildSolution (collisionBanach hd s hs) x
        ((8 * (‖collisionBanach hd s hs‖ + 1) * ‖x‖ ^ 2)⁻¹) u := by
  obtain ⟨u, h₀, hu⟩ := exists_cubic_solution (collisionBanach hd s hs) hx
  refine ⟨u, h₀, ?_⟩
  have H := cubic_solution_isMild _ hu
  rw [h₀] at H
  exact H

/-- Uniqueness for the weighted L² mild equation on any common closed time interval. -/
theorem weightedL2_mild_solution_unique (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) {x : WeightedL2Space d} {b : ℝ} (hb : 0 ≤ b)
    {u v : ℝ → WeightedL2Space d}
    (hu : IsCubicMildSolution (collisionBanach hd s hs) x b u)
    (hv : IsCubicMildSolution (collisionBanach hd s hs) x b v) : EqOn u v (Icc 0 b) := by
  apply cubic_solution_unique (collisionBanach hd s hs) hu.hasDerivWithinAt hv.hasDerivWithinAt
  have h₀ : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb⟩
  have hu₀ : u 0 = x := by simpa only [intervalIntegral.integral_same, add_zero] using hu.2 0 h₀
  have hv₀ : v 0 = x := by simpa only [intervalIntegral.integral_same, add_zero] using hv.2 0 h₀
  exact hu₀.trans hv₀.symm

/-- For Schwartz data the lifespan denominator uses exactly the frozen weighted norm. -/
theorem cubicLifespan_weightedSchwartz (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (f : 𝓢(Mom d, ℝ)) :
    cubicLifespan (collisionBanach hd s hs) (weightedToL2CLM s f) =
      (8 * (‖collisionBanach hd s hs‖ + 1) * weightedL2Norm s f ^ 2)⁻¹ := by
  simp only [cubicLifespan, norm_weightedToL2CLM]

end WaveTurbulence.WKEL2
