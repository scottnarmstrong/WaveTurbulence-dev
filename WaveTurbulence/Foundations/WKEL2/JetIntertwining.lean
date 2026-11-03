/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetCollisionBanach
public import WaveTurbulence.Foundations.WKEL2.CollisionPicard
public import WaveTurbulence.Foundations.WKEL2.DenseTripleEquality

/-!
# Compatibility of completed weighted jets with the base collision equation

The identity is proved on Schwartz inputs and extended by joint continuity
and the proved density in each of the three input variables.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance intertwineL2AddGroup : AddCommGroup (WeightedL2Space d) :=
  (inferInstance : NormedAddCommGroup (WeightedL2Space d)).toAddCommGroup
local instance intertwineL2Module : Module ℝ (WeightedL2Space d) :=
  (inferInstance : NormedSpace ℝ (WeightedL2Space d)).toModule

local instance intertwineNormedJet (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance intertwineSpaceJet (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance intertwineNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance intertwineSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance intertwineNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance intertwineSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- The zero coordinate is the underlying exact weighted L² function. -/
@[expose] def weightedSobolevToL2CLM (s : ℝ) (m : ℕ) :
    WeightedSobolevSpace d s m →L[ℝ] WeightedL2Space d :=
  weightedSobolevCoordinateCLM s m (zeroJetIndex d m)

theorem weightedSobolevToL2CLM_schwartz (s : ℝ) (m : ℕ) (f : 𝓢(Mom d, ℝ)) :
    weightedSobolevToL2CLM s m (schwartzToWeightedSobolevCLM s m f) = weightedToL2CLM s f := by
  rw [weightedSobolevToL2CLM, weightedSobolevCoordinateCLM_schwartz]
  simp only [zeroJetIndex, List.ofFn_zero, jetWordCLM_nil]

/-- The finite-jet collision field projects to the base weighted L² collision field. -/
theorem weightedSobolevToL2CLM_collision (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) (u v w : WeightedSobolevSpace d s m) :
    weightedSobolevToL2CLM s m (jetCollisionBanach hd s hs m u v w) =
      collisionBanach hd s hs (weightedSobolevToL2CLM s m u)
        (weightedSobolevToL2CLM s m v) (weightedSobolevToL2CLM s m w) := by
  apply dense_triple_ext (denseRange_schwartzToWeightedSobolevCLM (d := d) s m)
      (x := u) (y := v) (z := w)
  · fun_prop
  · fun_prop
  · intro f g h
    have H₁ := congrArg (weightedSobolevToL2CLM s m)
      (jetCollisionBanach_schwartz hd s hs m f g h)
    have H₂ := weightedSobolevToL2CLM_schwartz s m (WKE.collisionOpSchwartz (by omega) f g h)
    have H₃ := collisionBanach_schwartz hd s hs f g h
    simpa only [weightedSobolevToL2CLM_schwartz] using (H₁.trans H₂).trans H₃.symm

/-- Every differentiable finite-jet solution projects to a solution of the base equation. -/
theorem hasDerivWithinAt_weightedSobolevToL2 (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) {u : ℝ → WeightedSobolevSpace d s m}
    {S : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u (cubicField (jetCollisionBanach hd s hs m) (u t)) S t) :
    HasDerivWithinAt (fun r => weightedSobolevToL2CLM s m (u r))
      (cubicField (collisionBanach hd s hs) (weightedSobolevToL2CLM s m (u t))) S t := by
  have H := (weightedSobolevToL2CLM s m).hasFDerivAt.comp_hasDerivWithinAt t hu
  simpa only [Function.comp_def, cubicField, weightedSobolevToL2CLM_collision] using H

end WaveTurbulence.WKEL2
