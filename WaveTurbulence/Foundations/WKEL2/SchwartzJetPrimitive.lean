/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetRestriction
public import WaveTurbulence.Foundations.WKEL2.SchwartzReconstruction
public import WaveTurbulence.Foundations.WKEL2.CubicMild

/-!
# Compatible Bochner primitives of a continuous Schwartz collision curve
-/

public section

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance primitiveNormedJet (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance primitiveSpaceJet (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance primitiveNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance primitiveSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance primitiveNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance primitiveSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- The genuine Bochner primitive of the collision field in each completed jet order. -/
@[expose] def schwartzJetPrimitive (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s)
    (φin : 𝓢(Mom d, ℝ)) (φ : ℝ → 𝓢(Mom d, ℝ)) (t : ℝ) (m : ℕ) :
    WeightedSobolevSpace d s m :=
  schwartzToWeightedSobolevCLM s m φin + ∫ r in (0 : ℝ)..t,
    cubicField (jetCollisionBanach hd s hs m) (schwartzToWeightedSobolevCLM s m (φ r))

/-- Continuity in Schwartz space supplies actual Bochner integrability at every finite order. -/
theorem intervalIntegrable_schwartzJetField (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) {b t : ℝ} {φ : ℝ → 𝓢(Mom d, ℝ)}
    (hφ : ContinuousOn φ (Icc 0 b)) (ht : t ∈ Icc 0 b) :
    IntervalIntegrable (fun r => cubicField (jetCollisionBanach hd s hs m)
      (schwartzToWeightedSobolevCLM s m (φ r))) volume 0 t := by
  have H : ContinuousOn (fun r => cubicField (jetCollisionBanach hd s hs m)
      (schwartzToWeightedSobolevCLM s m (φ r))) (Icc 0 t) :=
    ((continuous_cubicField _).comp_continuousOn
    ((schwartzToWeightedSobolevCLM s m).continuous.comp_continuousOn hφ)).mono
    (Icc_subset_Icc le_rfl ht.2)
  exact H.intervalIntegrable_of_Icc ht.1

/-- The collision primitives at all finite orders form a compatible differential jet. -/
theorem isCompatible_schwartzJetPrimitive (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (φin : 𝓢(Mom d, ℝ)) {φ : ℝ → 𝓢(Mom d, ℝ)}
    {b t : ℝ} (hφ : ContinuousOn φ (Icc 0 b)) (ht : t ∈ Icc 0 b) :
    IsCompatibleWeightedJets s (schwartzJetPrimitive hd s hs φin φ t) := by
  intro m r hrm
  unfold schwartzJetPrimitive
  rw [map_add, weightedSobolevForgetCLM_schwartz,
    ← (weightedSobolevForgetCLM s m r hrm).intervalIntegral_comp_comm
      (intervalIntegrable_schwartzJetField hd s hs m hφ ht)]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [cubicField, weightedSobolevForgetCLM_collision, weightedSobolevForgetCLM_schwartz]

end WaveTurbulence.WKEL2
