/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzContinuation

/-!
# Exact equivalence of source Schwartz solutions and weighted L² mild solutions

The reconstructed source solution has the given Banach trajectory, by
uniqueness. Thus the correspondence identifies actual curves, not merely
the existence of two unrelated solutions with the same initial data.
-/

public section

noncomputable section

open Set
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

local instance equivalenceL2AddGroup : AddCommGroup (WeightedL2Space d) :=
  (inferInstance : NormedAddCommGroup (WeightedL2Space d)).toAddCommGroup
local instance equivalenceL2Module : Module ℝ (WeightedL2Space d) :=
  (inferInstance : NormedSpace ℝ (WeightedL2Space d)).toModule
/-- Every base mild trajectory with Schwartz data has its actual source Schwartz representative. -/
theorem exists_isWKESolution_eq_base_mild (hd : 3 ≤ d) (s : ℝ) (hs₀ : 0 ≤ s)
    (hs : (d : ℝ) / 2 - 1 < s) (φin : 𝓢(Mom d, ℝ)) {b : ℝ} (hb : 0 ≤ b)
    {u : ℝ → WeightedL2Space d}
    (hu : IsCubicMildSolution (collisionBanach hd s hs) (weightedToL2CLM s φin) b u) :
    ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin b φ ∧
      EqOn (fun t => weightedToL2CLM s (φ t)) u (Icc 0 b) := by
  have hu₀ : u 0 = weightedToL2CLM s φin := by
    simpa only [intervalIntegral.integral_same, add_zero] using hu.2 0 ⟨le_rfl, hb⟩
  obtain ⟨φ, hφ⟩ := exists_isWKESolution_of_base hd s hs₀ hs φin hb hu₀ hu.hasDerivWithinAt
  refine ⟨φ, hφ, ?_⟩
  have H := IsWKESolution.isWeightedL2Mild hd s hs₀ hs hb hφ
  apply cubic_solution_unique (collisionBanach hd s hs) H.hasDerivWithinAt hu.hasDerivWithinAt
  exact (congrArg (weightedToL2CLM s) hφ.2.1).trans hu₀.symm

/-- The frozen pointwise Schwartz solution class is exactly the base weighted L² mild equation. -/
theorem isWKESolution_iff_weightedL2Mild (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) {φin : 𝓢(Mom d, ℝ)} {b : ℝ} (hb : 0 ≤ b)
    (φ : ℝ → 𝓢(Mom d, ℝ)) :
    IsWKESolution φin b φ ↔ IsCubicMildSolution (collisionBanach hd s hs)
      (weightedToL2CLM s φin) b (fun t => weightedToL2CLM s (φ t)) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs₀ : 0 ≤ s := by linarith only [hdR, hs]
  constructor
  · exact IsWKESolution.isWeightedL2Mild hd s hs₀ hs hb
  · intro hu
    obtain ⟨ψ, hψ, hemb⟩ := exists_isWKESolution_eq_base_mild hd s hs₀ hs φin hb hu
    have heq : EqOn φ ψ (Icc 0 b) :=
      fun t ht => weightedToL2CLM_injective s (hemb ht).symm
    refine ⟨hψ.1.congr heq, (heq ⟨le_rfl, hb⟩).trans hψ.2.1, ?_⟩
    intro t ht k
    rw [heq ht]
    exact (hψ.2.2 t ht k).congr_of_mem (fun r hr => congrArg (fun f : 𝓢(Mom d, ℝ) => f k) (heq hr)) ht

end WaveTurbulence.WKEL2
