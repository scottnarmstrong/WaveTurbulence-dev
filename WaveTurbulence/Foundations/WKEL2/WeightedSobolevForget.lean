/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.LowerJets

/-!
# Bounded restriction from higher to lower completed weighted jet spaces
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance forgetNormedCore (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedJetCore d s m) := inferInstance
local instance forgetSpaceCore (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedJetCore d s m) := inferInstance
local instance forgetNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance forgetSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance

/-- Actual finite Schwartz jet norms are monotone in their order. -/
theorem norm_weightedJet_mono (s : ℝ) {r m : ℕ} (hrm : r ≤ m) (f : 𝓢(Mom d, ℝ)) :
    ‖weightedJetCLM s r f‖ ≤ ‖weightedJetCLM s m f‖ := by
  have H := norm_weightedSobolevLowerJetCLM_le s m r hrm (schwartzToWeightedSobolevCLM s m f)
  simpa only [weightedSobolevLowerJetCLM_schwartz, norm_schwartzToWeightedSobolevCLM] using H

/-- Restrict a core jet by decoding its unique Schwartz representative. -/
@[expose] def weightedJetCoreForgetLM (s : ℝ) (m r : ℕ) :
    WeightedJetCore d s m →ₗ[ℝ] WeightedSobolevSpace d s r :=
  (schwartzToWeightedSobolevCLM s r).toLinearMap.comp (weightedJetCoreDecode s m)

theorem norm_weightedJetCoreForgetLM_le (s : ℝ) {m r : ℕ} (hrm : r ≤ m)
    (u : WeightedJetCore d s m) : ‖weightedJetCoreForgetLM s m r u‖ ≤ ‖u‖ := by
  change ‖schwartzToWeightedSobolevCLM s r (weightedJetCoreDecode s m u)‖ ≤ _
  rw [norm_schwartzToWeightedSobolevCLM]
  exact (norm_weightedJet_mono s hrm _).trans_eq (norm_weightedJetCLM_coreDecode s m u)

/-- The core restriction is bounded with norm at most one. -/
@[expose] def weightedJetCoreForgetCLM (s : ℝ) (m r : ℕ) (hrm : r ≤ m) :
    WeightedJetCore d s m →L[ℝ] WeightedSobolevSpace d s r :=
  (weightedJetCoreForgetLM s m r).mkContinuous 1
    (fun u => by simpa only [one_mul] using norm_weightedJetCoreForgetLM_le s hrm u)

/-- Canonical bounded restriction between the completed weighted jet spaces. -/
@[expose] def weightedSobolevForgetCLM (s : ℝ) (m r : ℕ) (hrm : r ≤ m) :
    WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s r :=
  denseExtensionCLM (V := WeightedJetCore d s m) (E := WeightedSobolevSpace d s m)
    (F := WeightedSobolevSpace d s r) (weightedJetCoreInclusion s m)
    (denseRange_weightedJetCoreInclusion s m) (weightedJetCoreForgetCLM s m r hrm)

/-- Restriction agrees with the actual lower jet of every Schwartz input. -/
theorem weightedSobolevForgetCLM_schwartz (s : ℝ) {m r : ℕ} (hrm : r ≤ m)
    (f : 𝓢(Mom d, ℝ)) :
    weightedSobolevForgetCLM s m r hrm (schwartzToWeightedSobolevCLM s m f) =
      schwartzToWeightedSobolevCLM s r f := by
  have H := denseExtensionCLM_apply (V := WeightedJetCore d s m)
    (E := WeightedSobolevSpace d s m) (F := WeightedSobolevSpace d s r)
    (weightedJetCoreInclusion s m) (denseRange_weightedJetCoreInclusion s m)
    (weightedJetCoreForgetCLM s m r hrm) (weightedJetCoreEquiv s m f)
  simp only [← schwartzToWeightedSobolevCLM_eq_inclusion] at H
  change weightedSobolevForgetCLM s m r hrm _ = _ at H
  refine H.trans ?_
  simp only [weightedJetCoreForgetCLM, weightedJetCoreForgetLM,
    LinearMap.mkContinuous_apply, LinearMap.comp_apply, weightedJetCoreDecode,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  rfl

/-- Completed restriction never increases the norm. -/
theorem norm_weightedSobolevForgetCLM_le (s : ℝ) {m r : ℕ} (hrm : r ≤ m)
    (u : WeightedSobolevSpace d s m) : ‖weightedSobolevForgetCLM s m r hrm u‖ ≤ ‖u‖ := by
  have hcore : ‖weightedJetCoreForgetCLM (d := d) s m r hrm‖ ≤ 1 := by
    apply LinearMap.mkContinuous_norm_le _ zero_le_one
  have H : ‖weightedSobolevForgetCLM (d := d) s m r hrm‖ ≤ 1 :=
    (norm_denseExtensionCLM_apply_le _ _ _).trans hcore
  exact ((weightedSobolevForgetCLM s m r hrm).le_opNorm u).trans
    ((mul_le_mul_of_nonneg_right H (norm_nonneg _)).trans_eq (one_mul _))

end WaveTurbulence.WKEL2
