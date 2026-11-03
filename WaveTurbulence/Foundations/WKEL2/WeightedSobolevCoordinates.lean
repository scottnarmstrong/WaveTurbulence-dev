/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedSobolevModel
public import WaveTurbulence.Foundations.WKEL2.DenseIsometryExtension

/-!
# Faithful L² coordinates of completed weighted Sobolev jets
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The completion is realized isometrically in its actual finite L² jet product. -/
@[expose] def weightedSobolevJetIsometry (s : ℝ) (m : ℕ) :
    WeightedSobolevSpace d s m →ₗᵢ[ℝ]
      (JetIndex d m → Lp ℝ 2 (volume : Measure (Mom d))) :=
  denseIsometryExtension (V := WeightedJetCore d s m)
    (E := WeightedSobolevSpace d s m)
    (F := JetIndex d m → Lp ℝ 2 (volume : Measure (Mom d)))
    (weightedJetCoreInclusion (d := d) s m)
    (denseRange_weightedJetCoreInclusion (d := d) s m) (weightedJetRange d s m).subtypeₗᵢ

/-- The realized completed jet agrees with every original core jet. -/
theorem weightedSobolevJetIsometry_core (s : ℝ) (m : ℕ) (u : WeightedJetCore d s m) :
    weightedSobolevJetIsometry s m (weightedJetCoreInclusion s m u) = u.val := by
  unfold weightedSobolevJetIsometry
  rw [denseIsometryExtension_apply]
  rfl

/-- The realized Schwartz jet is its exact collection of weighted derivative coordinates. -/
theorem weightedSobolevJetIsometry_schwartz (s : ℝ) (m : ℕ) (f : 𝓢(Mom d, ℝ)) :
    weightedSobolevJetIsometry s m (schwartzToWeightedSobolevCLM s m f) =
      weightedJetCLM s m f := by
  change weightedSobolevJetIsometry s m (weightedJetCoreInclusion s m
    (weightedJetCoreCLM s m f)) = _
  rw [weightedSobolevJetIsometry_core]
  rfl

/-- Extract a derivative and moment coordinate as a continuous L²-valued linear map. -/
@[expose] def weightedSobolevCoordinateCLM (s : ℝ) (m : ℕ) (i : JetIndex d m) :
    WeightedSobolevSpace d s m →L[ℝ] Lp ℝ 2 (volume : Measure (Mom d)) :=
  (ContinuousLinearMap.proj i).comp (weightedSobolevJetIsometry s m).toContinuousLinearMap

/-- Coordinates on Schwartz inputs are the actual weighted differential expressions. -/
theorem weightedSobolevCoordinateCLM_schwartz (s : ℝ) (m : ℕ)
    (i : JetIndex d m) (f : 𝓢(Mom d, ℝ)) :
    weightedSobolevCoordinateCLM s m i (schwartzToWeightedSobolevCLM s m f) =
      weightedToL2CLM s (jetWordCLM (List.ofFn i.2) f) := by
  change weightedSobolevJetIsometry s m (schwartzToWeightedSobolevCLM s m f) i = _
  rw [weightedSobolevJetIsometry_schwartz, weightedJetCLM_apply]

/-- Every coordinate is bounded by the completed finite-jet norm. -/
theorem norm_weightedSobolevCoordinateCLM_le (s : ℝ) (m : ℕ) (i : JetIndex d m)
    (u : WeightedSobolevSpace d s m) : ‖weightedSobolevCoordinateCLM s m i u‖ ≤ ‖u‖ := by
  change ‖weightedSobolevJetIsometry s m u i‖ ≤ ‖u‖
  exact (norm_le_pi_norm _ i).trans_eq ((weightedSobolevJetIsometry s m).norm_map u)

end WaveTurbulence.WKEL2
