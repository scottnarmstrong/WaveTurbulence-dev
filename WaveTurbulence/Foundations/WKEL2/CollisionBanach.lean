/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CollisionCore
public import WaveTurbulence.Foundations.WKEL2.DenseTrilinearExtension

/-!
# The continuous collision trilinear map on weighted L²

This is the extension of the actual Schwartz collision operator along its
proved dense isometric image. Its Banach norm is the frozen weighted norm.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

/-- The exact weighted L² Banach model, in weighted coordinates. -/
abbrev WeightedL2Space (d : ℕ) := Lp ℝ 2 (volume : Measure (Mom d))

variable {d : ℕ}

local instance normedCoreOutput (s : ℝ) :
    NormedAddCommGroup (WeightedSchwartzCore d s →L[ℝ] WeightedL2Space d) := inferInstance
local instance spaceCoreOutput (s : ℝ) :
    NormedSpace ℝ (WeightedSchwartzCore d s →L[ℝ] WeightedL2Space d) := inferInstance
local instance normedCoreOutput₂ (s : ℝ) :
    NormedAddCommGroup (WeightedSchwartzCore d s →L[ℝ]
      WeightedSchwartzCore d s →L[ℝ] WeightedL2Space d) := inferInstance
local instance spaceCoreOutput₂ (s : ℝ) :
    NormedSpace ℝ (WeightedSchwartzCore d s →L[ℝ]
      WeightedSchwartzCore d s →L[ℝ] WeightedL2Space d) := inferInstance

/-- The bounded collision operator on the dense Schwartz core. -/
@[expose] def collisionCoreCLM (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) :
    WeightedSchwartzCore d s →L[ℝ] WeightedSchwartzCore d s →L[ℝ]
      WeightedSchwartzCore d s →L[ℝ] WeightedL2Space d :=
  boundedTrilinear (collisionCoreLinear (by omega) s)
    (exists_collisionCore_bound hd s hs).choose
    (exists_collisionCore_bound hd s hs).choose_spec.1
    (exists_collisionCore_bound hd s hs).choose_spec.2

/-- The collision trilinear map on the complete exact weighted L² model. -/
@[expose] def collisionBanach (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) :
    WeightedL2Space d →L[ℝ] WeightedL2Space d →L[ℝ]
      WeightedL2Space d →L[ℝ] WeightedL2Space d :=
  denseTrilinearExtension (weightedSchwartzCoreInclusion s)
    (denseRange_weightedSchwartzCoreInclusion s) (collisionCoreCLM hd s hs)

/-- The extension takes Schwartz inputs to the exact weighted embedding of their collision. -/
theorem collisionBanach_schwartz (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s)
    (f g h : 𝓢(Mom d, ℝ)) :
    collisionBanach hd s hs (weightedToL2CLM s f) (weightedToL2CLM s g)
      (weightedToL2CLM s h) = weightedToL2CLM s (WKE.collisionOpSchwartz (by omega) f g h) := by
  have H := denseTrilinearExtension_apply (weightedSchwartzCoreInclusion s)
    (denseRange_weightedSchwartzCoreInclusion s) (collisionCoreCLM hd s hs)
    (weightedSchwartzCoreEquiv s f) (weightedSchwartzCoreEquiv s g)
    (weightedSchwartzCoreEquiv s h)
  simp only [weightedSchwartzCoreInclusion_equiv] at H
  change collisionBanach hd s hs _ _ _ = _ at H
  refine H.trans ?_
  simp only [collisionCoreCLM, boundedTrilinear_apply, collisionCoreLinear,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, weightedSchwartzCoreDecode,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply, schwartzCollisionLinear_apply]
  rfl

end WaveTurbulence.WKEL2
