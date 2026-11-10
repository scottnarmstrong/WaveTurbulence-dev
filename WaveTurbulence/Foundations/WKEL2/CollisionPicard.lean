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

end WaveTurbulence.WKEL2
