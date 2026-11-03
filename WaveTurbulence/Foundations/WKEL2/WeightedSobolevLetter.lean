/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedSobolevForget
public import WaveTurbulence.Foundations.WKEL2.JetWordComponents

/-!
# Closed elementary operators on the completed weighted jet scale
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance letterNormedCore (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedJetCore d s m) := inferInstance
local instance letterSpaceCore (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedJetCore d s m) := inferInstance
local instance letterNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance letterSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance

/-- Apply one genuine coordinate moment or derivative to a Schwartz core jet. -/
@[expose] def weightedJetCoreLetterLM (s : ℝ) (m M : ℕ) (a : JetLetter d) :
    WeightedJetCore d s M →ₗ[ℝ] WeightedSobolevSpace d s m :=
  (schwartzToWeightedSobolevCLM s m).toLinearMap.comp
    ((jetLetterCLM a).toLinearMap.comp (weightedJetCoreDecode s M))

/-- Each elementary differential or moment operator loses precisely one jet order. -/
theorem norm_weightedJetCoreLetterLM_le (s : ℝ) (m M : ℕ) (hm : m + 1 ≤ M) (a : JetLetter d)
    (u : WeightedJetCore d s M) : ‖weightedJetCoreLetterLM s m M a u‖ ≤ ‖u‖ := by
  change ‖schwartzToWeightedSobolevCLM s m (jetLetterCLM a (weightedJetCoreDecode s M u))‖ ≤ _
  rw [norm_schwartzToWeightedSobolevCLM]
  have H := norm_weightedJet_jetWord_le s m M [a] (by simpa using hm)
    (weightedJetCoreDecode s M u)
  simpa only [jetWordCLM_cons, jetWordCLM_nil, norm_weightedJetCLM_coreDecode] using H

/-- Bounded elementary operator on the dense jet core. -/
@[expose] def weightedJetCoreLetterCLM (s : ℝ) (m M : ℕ) (hm : m + 1 ≤ M) (a : JetLetter d) :
    WeightedJetCore d s M →L[ℝ] WeightedSobolevSpace d s m :=
  (weightedJetCoreLetterLM s m M a).mkContinuous 1
    (fun u => by simpa only [one_mul] using norm_weightedJetCoreLetterLM_le s m M hm a u)

/-- Genuine coordinate multiplication or differentiation on the completed jet scale. -/
@[expose] def weightedSobolevLetterCLM (s : ℝ) (m M : ℕ) (hm : m + 1 ≤ M) (a : JetLetter d) :
    WeightedSobolevSpace d s M →L[ℝ] WeightedSobolevSpace d s m :=
  denseExtensionCLM (V := WeightedJetCore d s M) (E := WeightedSobolevSpace d s M)
    (F := WeightedSobolevSpace d s m) (weightedJetCoreInclusion (d := d) s M)
    (denseRange_weightedJetCoreInclusion (d := d) s M) (weightedJetCoreLetterCLM (d := d) s m M hm a)

/-- The completed operator agrees with the actual moment or derivative on Schwartz functions. -/
theorem weightedSobolevLetterCLM_schwartz (s : ℝ) (m M : ℕ) (hm : m + 1 ≤ M) (a : JetLetter d)
    (f : 𝓢(Mom d, ℝ)) :
    weightedSobolevLetterCLM s m M hm a (schwartzToWeightedSobolevCLM s M f) =
      schwartzToWeightedSobolevCLM s m (jetLetterCLM a f) := by
  have H := denseExtensionCLM_apply (V := WeightedJetCore d s M)
    (E := WeightedSobolevSpace d s M) (F := WeightedSobolevSpace d s m)
    (weightedJetCoreInclusion (d := d) s M) (denseRange_weightedJetCoreInclusion (d := d) s M)
    (weightedJetCoreLetterCLM (d := d) s m M hm a) (weightedJetCoreEquiv s M f)
  simp only [← schwartzToWeightedSobolevCLM_eq_inclusion] at H
  change weightedSobolevLetterCLM s m M hm a _ = _ at H
  refine H.trans ?_
  simp only [weightedJetCoreLetterCLM, weightedJetCoreLetterLM,
    LinearMap.mkContinuous_apply, LinearMap.comp_apply, weightedJetCoreDecode,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  rfl

end WaveTurbulence.WKEL2
