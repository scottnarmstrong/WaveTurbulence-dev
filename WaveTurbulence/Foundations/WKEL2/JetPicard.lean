/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetIntertwining

/-!
# Local well-posedness in every complete weighted derivative and moment space
-/

public section

noncomputable section

open Set

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance jetPicardNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance jetPicardSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance jetPicardNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance jetPicardSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance jetPicardNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance jetPicardSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- A finite-jet mild solution projects to a mild solution of the base weighted L² equation. -/
theorem jet_mild_solution_projects (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) {x : WeightedSobolevSpace d s m}
    {b : ℝ} (hb : 0 ≤ b) {u : ℝ → WeightedSobolevSpace d s m}
    (hu : IsCubicMildSolution (jetCollisionBanach hd s hs m) x b u) :
    IsCubicMildSolution (collisionBanach hd s hs) (weightedSobolevToL2CLM s m x) b
      (fun r => weightedSobolevToL2CLM s m (u r)) := by
  have H := cubic_solution_isMild (collisionBanach hd s hs)
    (fun t ht => hasDerivWithinAt_weightedSobolevToL2 hd s hs m (hu.hasDerivWithinAt t ht))
  have h₀ : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb⟩
  have hu₀ : u 0 = x := by simpa only [intervalIntegral.integral_same, add_zero] using hu.2 0 h₀
  simpa only [hu₀] using H

end WaveTurbulence.WKEL2
