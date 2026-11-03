/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzContinuation

/-!
# Equality of Schwartz, weighted L², and all finite weighted-jet maximal times
-/

public section

noncomputable section

open Set
open scoped SchwartzMap ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance maximalL2AddGroup : AddCommGroup (WeightedL2Space d) :=
  (inferInstance : NormedAddCommGroup (WeightedL2Space d)).toAddCommGroup
local instance maximalL2Module : Module ℝ (WeightedL2Space d) :=
  (inferInstance : NormedSpace ℝ (WeightedL2Space d)).toModule
local instance maximalNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance maximalSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance maximalNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance maximalSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance maximalNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance maximalSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- Maximal positive lifespan of the actual weighted L² Banach equation. -/
@[expose] def weightedL2TauMax (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s)
    (φin : 𝓢(Mom d, ℝ)) : ℝ≥0∞ :=
  ⨆ (T : ℝ) (_ : 0 < T ∧ ∃ u : ℝ → WeightedL2Space d,
    u 0 = weightedToL2CLM s φin ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt u (cubicField (collisionBanach hd s hs) (u t)) (Icc 0 T) t), ENNReal.ofReal T

/-- Maximal positive lifespan of the completed finite weighted-jet equation. -/
@[expose] def weightedSobolevTauMax (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s)
    (m : ℕ) (φin : 𝓢(Mom d, ℝ)) : ℝ≥0∞ :=
  ⨆ (T : ℝ) (_ : 0 < T ∧ ∃ u : ℝ → WeightedSobolevSpace d s m,
    u 0 = schwartzToWeightedSobolevCLM s m φin ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt u (cubicField (jetCollisionBanach hd s hs m) (u t)) (Icc 0 T) t), ENNReal.ofReal T

/-- The base weighted L² maximal time equals the landed source Schwartz maximal time. -/
theorem weightedL2TauMax_eq_tauMax (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (φin : 𝓢(Mom d, ℝ)) :
    weightedL2TauMax hd s hs φin = WKE.tauMax φin := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs₀ : 0 ≤ s := by linarith only [hdR, hs]
  apply le_antisymm
  · unfold weightedL2TauMax
    apply iSup₂_le
    intro T ⟨hT, u, hu₀, hu⟩
    obtain ⟨φ, hφ⟩ := exists_isWKESolution_of_base hd s hs₀ hs φin hT.le hu₀ hu
    exact WKE.ofReal_le_tauMax hT hφ
  · unfold WKE.tauMax weightedL2TauMax
    apply iSup₂_le
    intro T ⟨hT, φ, hφ⟩
    have H := IsWKESolution.isWeightedL2Mild hd s hs₀ hs hT.le hφ
    exact le_iSup₂_of_le T ⟨hT, (fun t => weightedToL2CLM s (φ t)),
      congrArg (weightedToL2CLM s) hφ.2.1, H.hasDerivWithinAt⟩ le_rfl

/-- Every finite weighted moment and derivative maximal time equals the same Schwartz maximal time. -/
theorem weightedSobolevTauMax_eq_tauMax (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) (φin : 𝓢(Mom d, ℝ)) :
    weightedSobolevTauMax hd s hs m φin = WKE.tauMax φin := by
  rw [← weightedL2TauMax_eq_tauMax hd s hs φin]
  apply le_antisymm
  · unfold weightedSobolevTauMax weightedL2TauMax
    apply iSup₂_le
    intro T ⟨hT, u, hu₀, hu⟩
    exact le_iSup₂_of_le T ⟨hT, (fun t => weightedSobolevToL2CLM s m (u t)),
      (by simp only [hu₀, weightedSobolevToL2CLM_schwartz]),
      (fun t ht => hasDerivWithinAt_weightedSobolevToL2 hd s hs m (hu t ht))⟩ le_rfl
  · unfold weightedL2TauMax weightedSobolevTauMax
    apply iSup₂_le
    intro T ⟨hT, v, hv₀, hv⟩
    obtain ⟨u, hu₀, hu⟩ := exists_jet_solution_of_base hd s hs m φin hT.le hv₀ hv
    exact le_iSup₂_of_le T ⟨hT, u, hu₀, hu⟩ le_rfl

end WaveTurbulence.WKEL2
