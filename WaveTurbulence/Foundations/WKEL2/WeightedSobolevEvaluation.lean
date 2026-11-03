/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedSobolevForget
public import WaveTurbulence.Foundations.WKEL2.SchwartzPointEvaluation

/-!
# Bounded point evaluation on sufficiently high completed jets
-/

public section

noncomputable section

open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance evaluationNormedCore (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedJetCore d s m) := inferInstance
local instance evaluationSpaceCore (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedJetCore d s m) := inferInstance
local instance evaluationNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance evaluationSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance

/-- Point evaluation on the actual Schwartz jet core. -/
@[expose] def weightedJetCoreEvaluationLM (s : ℝ) (m : ℕ) (k : Mom d) :
    WeightedJetCore d s m →ₗ[ℝ] ℝ where
  toFun u := weightedJetCoreDecode s m u k
  map_add' u v := by simp only [map_add, _root_.add_apply]
  map_smul' c u := by simp only [map_smul, _root_.smul_apply]; rfl

/-- Sobolev evaluation is bounded uniformly in the evaluation point. -/
theorem norm_weightedJetCoreEvaluationLM_le (s : ℝ) (hs : 0 ≤ s) {m : ℕ} (hm : d ≤ m)
    (k : Mom d) (u : WeightedJetCore d s m) :
    ‖weightedJetCoreEvaluationLM s m k u‖ ≤ (2 : ℝ) ^ d * ‖u‖ := by
  apply (norm_apply_le_weightedJet s hs (weightedJetCoreDecode s m u) k).trans
  apply (mul_le_mul_of_nonneg_left (norm_weightedJet_mono s hm _) (by positivity)).trans_eq
  rw [norm_weightedJetCLM_coreDecode]

/-- Bounded evaluation on the core, with the proved dimension-only bound. -/
@[expose] def weightedJetCoreEvaluationCLM (s : ℝ) (hs : 0 ≤ s) {m : ℕ} (hm : d ≤ m)
    (k : Mom d) : WeightedJetCore d s m →L[ℝ] ℝ :=
  (weightedJetCoreEvaluationLM s m k).mkContinuous ((2 : ℝ) ^ d)
    (norm_weightedJetCoreEvaluationLM_le s hs hm k)

/-- The continuous point representative of a sufficiently high completed weighted jet. -/
@[expose] def weightedSobolevEvaluationCLM (s : ℝ) (hs : 0 ≤ s) {m : ℕ} (hm : d ≤ m)
    (k : Mom d) : WeightedSobolevSpace d s m →L[ℝ] ℝ :=
  denseExtensionCLM (V := WeightedJetCore d s m) (E := WeightedSobolevSpace d s m)
    (F := ℝ) (weightedJetCoreInclusion s m) (denseRange_weightedJetCoreInclusion s m)
    (weightedJetCoreEvaluationCLM s hs hm k)

/-- Completed evaluation recovers the actual value of every Schwartz function. -/
theorem weightedSobolevEvaluationCLM_schwartz (s : ℝ) (hs : 0 ≤ s) {m : ℕ}
    (hm : d ≤ m) (k : Mom d) (f : 𝓢(Mom d, ℝ)) :
    weightedSobolevEvaluationCLM s hs hm k (schwartzToWeightedSobolevCLM s m f) = f k := by
  have H := denseExtensionCLM_apply (V := WeightedJetCore d s m)
    (E := WeightedSobolevSpace d s m) (F := ℝ) (weightedJetCoreInclusion s m)
    (denseRange_weightedJetCoreInclusion s m) (weightedJetCoreEvaluationCLM s hs hm k)
    (weightedJetCoreEquiv s m f)
  simp only [← schwartzToWeightedSobolevCLM_eq_inclusion] at H
  change weightedSobolevEvaluationCLM s hs hm k _ = _ at H
  refine H.trans ?_
  simp only [weightedJetCoreEvaluationCLM, LinearMap.mkContinuous_apply,
    weightedJetCoreEvaluationLM, LinearMap.coe_mk, AddHom.coe_mk, weightedJetCoreDecode,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]

end WaveTurbulence.WKEL2
