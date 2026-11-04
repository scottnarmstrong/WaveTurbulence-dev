/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SolutionEquivalence

/-!
# Quantitative Schwartz existence on the exact weighted L² Picard lifespan
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance schwartzPicardNormedOp : NormedAddCommGroup
    (WeightedL2Space d →L[ℝ] WeightedL2Space d) := inferInstance
local instance schwartzPicardSpaceOp : NormedSpace ℝ
    (WeightedL2Space d →L[ℝ] WeightedL2Space d) := inferInstance
local instance schwartzPicardNormedOp₂ : NormedAddCommGroup
    (WeightedL2Space d →L[ℝ] WeightedL2Space d →L[ℝ] WeightedL2Space d) := inferInstance
local instance schwartzPicardSpaceOp₂ : NormedSpace ℝ
    (WeightedL2Space d →L[ℝ] WeightedL2Space d →L[ℝ] WeightedL2Space d) := inferInstance

/-- TARGET Appendix C: source Schwartz existence with inverse-square weighted L² lifespan. -/
theorem exists_isWKESolution_weighted_lifespan (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) {φin : 𝓢(Mom d, ℝ)} (hφin : φin ≠ 0) :
    ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin
      (8 * (‖collisionBanach hd s hs‖ + 1) * weightedL2Norm s φin ^ 2)⁻¹ φ := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs₀ : 0 ≤ s := by linarith only [hdR, hs]
  have hw : weightedToL2CLM s φin ≠ 0 := by
    intro h
    apply hφin
    apply weightedToL2CLM_injective s
    simpa only [map_zero] using h
  obtain ⟨u, hu₀, hu⟩ := exists_cubic_solution (collisionBanach hd s hs) hw
  have H := exists_isWKESolution_of_base hd s hs₀ hs φin
    (cubicLifespan_pos (collisionBanach hd s hs) hw).le hu₀ hu
  simpa only [cubicLifespan_weightedSchwartz] using H

end WaveTurbulence.WKEL2
