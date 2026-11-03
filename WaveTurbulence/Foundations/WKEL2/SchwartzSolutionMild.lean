/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzJetPrimitive
public import WaveTurbulence.Foundations.WKEL2.WeightedSobolevEvaluation
public import WaveTurbulence.Frozen.Defs.IsWKESolution

/-!
# Source-defined Schwartz solutions satisfy the actual Banach mild equations
-/

public section

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance sourceMildNormedJet (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance sourceMildSpaceJet (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance sourceMildNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance sourceMildSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance sourceMildNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance sourceMildSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- Evaluation of the completed collision field agrees with the frozen collision operator. -/
theorem weightedSobolevEvaluationCLM_field (hd : 3 ≤ d) (s : ℝ) (hs₀ : 0 ≤ s)
    (hs : (d : ℝ) / 2 - 1 < s) {m : ℕ} (hm : d ≤ m) (k : Mom d) (f : 𝓢(Mom d, ℝ)) :
    weightedSobolevEvaluationCLM s hs₀ hm k
      (cubicField (jetCollisionBanach hd s hs m) (schwartzToWeightedSobolevCLM s m f)) =
      collisionOp f f f k := by
  rw [cubicField, jetCollisionBanach_schwartz, weightedSobolevEvaluationCLM_schwartz]
  exact congrFun (WKE.coe_collisionOpSchwartz (by omega) f f f) k

/-- The source collision along a continuous Schwartz curve is continuous at every point. -/
theorem continuousOn_collisionOp_curve (hd : 3 ≤ d) (s : ℝ) (hs₀ : 0 ≤ s)
    (hs : (d : ℝ) / 2 - 1 < s) {φ : ℝ → 𝓢(Mom d, ℝ)} {b : ℝ}
    (hφ : ContinuousOn φ (Icc 0 b)) (k : Mom d) :
    ContinuousOn (fun t => collisionOp (φ t) (φ t) (φ t) k) (Icc 0 b) := by
  have H := (weightedSobolevEvaluationCLM s hs₀ (m := d) le_rfl k).continuous.comp_continuousOn
    ((continuous_cubicField (jetCollisionBanach hd s hs d)).comp_continuousOn
      ((schwartzToWeightedSobolevCLM s d).continuous.comp_continuousOn hφ))
  simpa only [Function.comp_def, weightedSobolevEvaluationCLM_field] using H

/-- The pointwise source ODE implies all genuine weighted-jet Bochner mild equations. -/
theorem IsWKESolution.isJetMild (hd : 3 ≤ d) (s : ℝ) (hs₀ : 0 ≤ s)
    (hs : (d : ℝ) / 2 - 1 < s) {φin : 𝓢(Mom d, ℝ)} {b : ℝ}
    {φ : ℝ → 𝓢(Mom d, ℝ)} (hφ : IsWKESolution φin b φ) (m : ℕ) :
    IsCubicMildSolution (jetCollisionBanach hd s hs m) (schwartzToWeightedSobolevCLM s m φin) b
      (fun t => schwartzToWeightedSobolevCLM s m (φ t)) := by
  refine ⟨(schwartzToWeightedSobolevCLM s m).continuous.comp_continuousOn hφ.1, fun t ht => ?_⟩
  obtain ⟨f, hf⟩ := exists_schwartz_of_compatible_jets s hs₀
    (schwartzJetPrimitive hd s hs φin φ t)
    (isCompatible_schwartzJetPrimitive hd s hs φin hφ.1 ht)
  have hfeq : f = φ t := by
    ext k
    have He := congrArg (weightedSobolevEvaluationCLM s hs₀ (m := d) le_rfl k) (hf d)
    rw [weightedSobolevEvaluationCLM_schwartz, schwartzJetPrimitive, map_add,
      weightedSobolevEvaluationCLM_schwartz,
      ← (weightedSobolevEvaluationCLM s hs₀ (m := d) le_rfl k).intervalIntegral_comp_comm
        (intervalIntegrable_schwartzJetField hd s hs d hφ.1 ht)] at He
    simp only [weightedSobolevEvaluationCLM_field] at He
    have hc : ContinuousOn (fun r => φ r k) (Icc 0 t) := by
      have H := (weightedSobolevEvaluationCLM s hs₀ (m := d) le_rfl k).continuous.comp_continuousOn
        ((schwartzToWeightedSobolevCLM s d).continuous.comp_continuousOn hφ.1)
      simpa only [Function.comp_def, weightedSobolevEvaluationCLM_schwartz] using
        H.mono (Icc_subset_Icc le_rfl ht.2)
    have hv := (continuousOn_collisionOp_curve hd s hs₀ hs hφ.1 k).mono
      (Icc_subset_Icc le_rfl ht.2)
    have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 hc
      (fun r hr => ((hφ.2.2 r ⟨hr.1.le, (hr.2.trans_le ht.2).le⟩ k).hasDerivAt
        (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2))).hasDerivWithinAt (s := Ioi r))
      (hv.intervalIntegrable_of_Icc ht.1)
    rw [H, hφ.2.1] at He
    linear_combination He
  rw [hfeq] at hf
  exact hf m

/-- No Schwartz information is lost by completion at any finite jet order. -/
theorem schwartzToWeightedSobolevCLM_injective (s : ℝ) (m : ℕ) :
    Function.Injective (schwartzToWeightedSobolevCLM (d := d) s m) := by
  intro f g h
  rw [schwartzToWeightedSobolevCLM_eq_inclusion, schwartzToWeightedSobolevCLM_eq_inclusion] at h
  exact (weightedJetCoreEquiv s m).injective ((weightedJetCoreInclusion s m).injective h)

/-- All completed jet mild equations reconstruct exactly the source Schwartz solution notion. -/
theorem isWKESolution_of_all_jetMild (hd : 3 ≤ d) (s : ℝ) (hs₀ : 0 ≤ s)
    (hs : (d : ℝ) / 2 - 1 < s) {φin : 𝓢(Mom d, ℝ)} {b : ℝ} (hb : 0 ≤ b)
    {φ : ℝ → 𝓢(Mom d, ℝ)}
    (hφ : ∀ m, IsCubicMildSolution (jetCollisionBanach hd s hs m)
      (schwartzToWeightedSobolevCLM s m φin) b (fun t => schwartzToWeightedSobolevCLM s m (φ t))) :
    IsWKESolution φin b φ := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    apply (tendsto_schwartz_iff_weightedSobolev s hs₀ φ (φ t)).2
    intro m
    exact (hφ m).1 t ht
  · apply schwartzToWeightedSobolevCLM_injective s 0
    simpa only [intervalIntegral.integral_same, add_zero] using (hφ 0).2 0 ⟨le_rfl, hb⟩
  · intro t ht k
    have H := (weightedSobolevEvaluationCLM s hs₀ (m := d) le_rfl k).hasFDerivAt.comp_hasDerivWithinAt t
      ((hφ d).hasDerivWithinAt t ht)
    simpa only [Function.comp_def, weightedSobolevEvaluationCLM_schwartz,
      weightedSobolevEvaluationCLM_field] using H

end WaveTurbulence.WKEL2
