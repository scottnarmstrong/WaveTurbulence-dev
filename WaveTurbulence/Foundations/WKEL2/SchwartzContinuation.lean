/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetPersistence
public import WaveTurbulence.Foundations.WKEL2.JetPicard
public import WaveTurbulence.Foundations.WKE.Lifespan

/-!
# Schwartz continuation with lifespan controlled only by the exact weighted L² norm
-/

public section

noncomputable section

open Set
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance schwartzContinueL2AddGroup : AddCommGroup (WeightedL2Space d) :=
  (inferInstance : NormedAddCommGroup (WeightedL2Space d)).toAddCommGroup
local instance schwartzContinueL2Module : Module ℝ (WeightedL2Space d) :=
  (inferInstance : NormedSpace ℝ (WeightedL2Space d)).toModule
local instance schwartzContinueNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance schwartzContinueSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance schwartzContinueNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance schwartzContinueSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance schwartzContinueNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance schwartzContinueSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- A source Schwartz solution satisfies the exact weighted L² Banach mild equation. -/
theorem IsWKESolution.isWeightedL2Mild (hd : 3 ≤ d) (s : ℝ) (hs₀ : 0 ≤ s)
    (hs : (d : ℝ) / 2 - 1 < s) {φin : 𝓢(Mom d, ℝ)} {b : ℝ} (hb : 0 ≤ b)
    {φ : ℝ → 𝓢(Mom d, ℝ)} (hφ : IsWKESolution φin b φ) :
    IsCubicMildSolution (collisionBanach hd s hs) (weightedToL2CLM s φin) b
      (fun t => weightedToL2CLM s (φ t)) := by
  have H := jet_mild_solution_projects hd s hs 0 hb (IsWKESolution.isJetMild hd s hs₀ hs hφ 0)
  simpa only [weightedSobolevToL2CLM_schwartz] using H

/-- Uniform Schwartz existence with a lifespan depending only on a bound for the base L² norm. -/
theorem exists_isWKESolution_uniform (hd : 3 ≤ d) (s : ℝ) (hs₀ : 0 ≤ s)
    (hs : (d : ℝ) / 2 - 1 < s) (φin : 𝓢(Mom d, ℝ)) {R : ℝ} (hR : 0 ≤ R)
    (hφin : weightedL2Norm s φin ≤ R) :
    ∃ φ : ℝ → 𝓢(Mom d, ℝ),
      IsWKESolution φin (cubicUniformStep (collisionBanach hd s hs) R) φ := by
  obtain ⟨v, hv₀, hv⟩ := exists_cubic_solution_uniform (collisionBanach hd s hs) (x := weightedToL2CLM s φin) hR
    (by simpa only [norm_weightedToL2CLM] using hφin)
  exact exists_isWKESolution_of_base hd s hs₀ hs φin (cubicUniformStep_pos _ hR).le hv₀ hv

/-- A bounded endpoint base norm extends the source solution by a uniform positive time. -/
theorem exists_isWKESolution_extension (hd : 3 ≤ d) (s : ℝ) (hs₀ : 0 ≤ s)
    (hs : (d : ℝ) / 2 - 1 < s) {φin : 𝓢(Mom d, ℝ)} {b R : ℝ}
    (hb : 0 ≤ b) (hR : 0 ≤ R) {φ : ℝ → 𝓢(Mom d, ℝ)}
    (hφ : IsWKESolution φin b φ) (hend : weightedL2Norm s (φ b) ≤ R) :
    ∃ ψ : ℝ → 𝓢(Mom d, ℝ),
      IsWKESolution φin (b + cubicUniformStep (collisionBanach hd s hs) R) ψ := by
  have hδ := cubicUniformStep_pos (collisionBanach hd s hs) hR
  have hu := IsWKESolution.isWeightedL2Mild hd s hs₀ hs hb hφ
  obtain ⟨w, hw, hwd⟩ := extend_cubic_solution (collisionBanach hd s hs) hR hb
    (le_add_of_nonneg_right hδ.le) le_rfl hu.hasDerivWithinAt
    (by simpa only [norm_weightedToL2CLM] using hend)
  apply exists_isWKESolution_of_base hd s hs₀ hs φin (by positivity) _ hwd
  exact (hw ⟨le_rfl, hb⟩).trans (congrArg (weightedToL2CLM s) hφ.2.1)

/-- Positivity of the landed maximal time also follows from weighted L² Picard and persistence. -/
theorem tauMax_pos_of_weightedPicard (hd : 3 ≤ d) (s : ℝ) (hs₀ : 0 ≤ s)
    (hs : (d : ℝ) / 2 - 1 < s) (φin : 𝓢(Mom d, ℝ)) : 0 < WKE.tauMax φin := by
  have hR := weightedL2Norm_nonneg s φin
  obtain ⟨φ, hφ⟩ := exists_isWKESolution_uniform hd s hs₀ hs φin hR le_rfl
  have hδ := cubicUniformStep_pos (collisionBanach hd s hs) hR
  exact (ENNReal.ofReal_pos.mpr hδ).trans_le (WKE.ofReal_le_tauMax hδ hφ)

end WaveTurbulence.WKEL2
