/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.JetAPriori
public import WaveTurbulence.Foundations.WKEL2.CubicContinuation
public import WaveTurbulence.Foundations.WKEL2.SchwartzJetSolutions

/-!
# Persistence of every finite weighted jet for the full base L² lifespan
-/

public section

noncomputable section

open Set
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance persistenceL2AddGroup : AddCommGroup (WeightedL2Space d) :=
  (inferInstance : NormedAddCommGroup (WeightedL2Space d)).toAddCommGroup
local instance persistenceL2Module : Module ℝ (WeightedL2Space d) :=
  (inferInstance : NormedSpace ℝ (WeightedL2Space d)).toModule
local instance persistenceNormedBase (s : ℝ) (m : ℕ) :
    NormedAddCommGroup (WeightedSobolevSpace d s m) := inferInstance
local instance persistenceSpaceBase (s : ℝ) (m : ℕ) :
    NormedSpace ℝ (WeightedSobolevSpace d s m) := inferInstance
local instance persistenceNormedOp (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance persistenceSpaceOp (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m) := inferInstance
local instance persistenceNormedOp₂ (s : ℝ) (m : ℕ) : NormedAddCommGroup
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance
local instance persistenceSpaceOp₂ (s : ℝ) (m : ℕ) : NormedSpace ℝ
    (WeightedSobolevSpace d s m →L[ℝ] WeightedSobolevSpace d s m →L[ℝ]
      WeightedSobolevSpace d s m) := inferInstance

/-- Every finite weighted derivative and moment solution persists for the full base interval. -/
theorem exists_jet_solution_of_base (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (m : ℕ) (φin : 𝓢(Mom d, ℝ))
    {T : ℝ} (hT : 0 ≤ T) {v : ℝ → WeightedL2Space d}
    (hv₀ : v 0 = weightedToL2CLM s φin)
    (hv : ∀ t ∈ Icc 0 T, HasDerivWithinAt v (cubicField (collisionBanach hd s hs) (v t))
      (Icc 0 T) t) :
    ∃ u : ℝ → WeightedSobolevSpace d s m, u 0 = schwartzToWeightedSobolevCLM s m φin ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt u (cubicField (jetCollisionBanach hd s hs m) (u t))
        (Icc 0 T) t := by
  have hvc : ContinuousOn v (Icc 0 T) := fun t ht => (hv t ht).continuousWithinAt
  obtain ⟨A₀, hA₀⟩ := (isCompact_Icc.image_of_continuousOn hvc).isBounded.exists_norm_le
  let A := max 0 A₀
  have hA : 0 ≤ A := le_max_left _ _
  have hAv : ∀ t ∈ Icc 0 T, ‖v t‖ ≤ A :=
    fun t ht => (hA₀ _ (mem_image_of_mem _ ht)).trans (le_max_right _ _)
  let B := ‖schwartzToWeightedSobolevCLM s m φin‖
  let H := exists_jet_solution_uniform_bound_on_subintervals hd s hs m T A B hT hA (norm_nonneg _)
  apply exists_cubic_solution_of_uniform_bound (jetCollisionBanach hd s hs m)
    (schwartzToWeightedSobolevCLM s m φin) (Q := H.choose) hT
  intro b hb hbT u hu₀ hu
  have hproj : EqOn (fun t => weightedSobolevToL2CLM s m (u t)) v (Icc 0 b) := by
    apply cubic_solution_unique (collisionBanach hd s hs)
      (fun t ht => hasDerivWithinAt_weightedSobolevToL2 hd s hs m (hu t ht))
      (fun t ht => (hv t ⟨ht.1, ht.2.trans hbT⟩).mono (Icc_subset_Icc le_rfl hbT))
    rw [hu₀, weightedSobolevToL2CLM_schwartz, hv₀]
  exact H.choose_spec.2 b hbT u hu (by rw [hu₀])
    (fun t ht => (congrArg norm (hproj ht)).le.trans (hAv t ⟨ht.1, ht.2.trans hbT⟩))

/-- A base weighted L² solution with Schwartz initial data lifts to a source Schwartz solution. -/
theorem exists_isWKESolution_of_base (hd : 3 ≤ d) (s : ℝ) (hs₀ : 0 ≤ s)
    (hs : (d : ℝ) / 2 - 1 < s) (φin : 𝓢(Mom d, ℝ)) {T : ℝ} (hT : 0 ≤ T)
    {v : ℝ → WeightedL2Space d} (hv₀ : v 0 = weightedToL2CLM s φin)
    (hv : ∀ t ∈ Icc 0 T, HasDerivWithinAt v (cubicField (collisionBanach hd s hs) (v t))
      (Icc 0 T) t) : ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin T φ := by
  classical
  choose U h₀ hU using fun m => exists_jet_solution_of_base hd s hs m φin hT hv₀ hv
  obtain ⟨φ, hφ, _⟩ := exists_isWKESolution_of_all_jet_solutions hd s hs₀ hs φin hT U h₀ hU
  exact ⟨φ, hφ⟩

end WaveTurbulence.WKEL2
