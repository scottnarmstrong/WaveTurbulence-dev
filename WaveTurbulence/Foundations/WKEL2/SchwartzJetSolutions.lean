/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzSolutionMild

/-!
# Reconstruction of Schwartz solutions from solutions at all finite jet orders
-/

public section

noncomputable section

open Set
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance liftNormedJet (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance liftSpaceJet (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance liftNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance liftSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance liftNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance liftSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- Existence at all finite orders gives an actual source-defined Schwartz solution. -/
theorem exists_isWKESolution_of_all_jet_solutions (hd : 3 ≤ d) (s : ℝ) (hs₀ : 0 ≤ s)
    (hs : (d : ℝ) / 2 - 1 < s) (φin : 𝓢(Mom d, ℝ)) {b : ℝ} (hb : 0 ≤ b)
    (U : ∀ m : ℕ, ℝ → WeightedSobolevSpace d s m)
    (h₀ : ∀ m, U m 0 = schwartzToWeightedSobolevCLM s m φin)
    (hU : ∀ m, ∀ t ∈ Icc 0 b, HasDerivWithinAt (U m)
      (cubicField (jetCollisionBanach hd s hs m) (U m t)) (Icc 0 b) t) :
    ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin b φ ∧
      ∀ t ∈ Icc 0 b, ∀ m, schwartzToWeightedSobolevCLM s m (φ t) = U m t := by
  classical
  have hcompat (t : ℝ) (ht : t ∈ Icc 0 b) : IsCompatibleWeightedJets s (fun m => U m t) := by
    intro m r hrm
    have H := cubic_solution_unique (jetCollisionBanach hd s hs r)
      (fun z hz => hasDerivWithinAt_weightedSobolevForget hd s hs hrm (hU m z hz)) (hU r)
      (by rw [h₀ m, weightedSobolevForgetCLM_schwartz, h₀ r])
    exact H ht
  have hex : ∀ t : ℝ, ∃ f : 𝓢(Mom d, ℝ),
      ∀ ht : t ∈ Icc 0 b, ∀ m, schwartzToWeightedSobolevCLM s m f = U m t := by
    intro t
    by_cases ht : t ∈ Icc 0 b
    · obtain ⟨f, hf⟩ := exists_schwartz_of_compatible_jets s hs₀ _ (hcompat t ht)
      exact ⟨f, fun _ => hf⟩
    · exact ⟨φin, fun h => (ht h).elim⟩
  choose φ hφ using hex
  refine ⟨φ, isWKESolution_of_all_jetMild hd s hs₀ hs hb (fun m => ?_), hφ⟩
  have hdφ : ∀ t ∈ Icc 0 b,
      HasDerivWithinAt (fun z => schwartzToWeightedSobolevCLM s m (φ z))
        (cubicField (jetCollisionBanach hd s hs m) (schwartzToWeightedSobolevCLM s m (φ t)))
        (Icc 0 b) t := by
    intro t ht
    rw [hφ t ht m]
    exact (hU m t ht).congr_of_mem (fun z hz => hφ z hz m) ht
  have H := cubic_solution_isMild (jetCollisionBanach hd s hs m) hdφ
  rw [hφ 0 ⟨le_rfl, hb⟩ m, h₀ m] at H
  exact H

end WaveTurbulence.WKEL2
