/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedL2
public import WaveTurbulence.Frozen.Defs.IsWKESolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# Schwartz data in the exact weighted L² space

The frozen multiplier has temperate growth for every real exponent. It
therefore acts continuously on Schwartz space, followed by the canonical
continuous embedding into real L².
-/

public section

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Multiplication by the exact frozen weight on Schwartz space. -/
@[expose] def weightedSchwartzCLM (s : ℝ) : 𝓢(Mom d, ℝ) →L[ℝ] 𝓢(Mom d, ℝ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ).flip
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Mom d) (s / 2))

/-- The weighted Schwartz map uses exactly the frozen multiplier. -/
theorem weightedSchwartzCLM_apply (s : ℝ) (f : 𝓢(Mom d, ℝ)) (k : Mom d) :
    weightedSchwartzCLM s f k = weightedFunction s f k := by
  rw [weightedSchwartzCLM, SchwartzMap.bilinLeftCLM_apply]
  rfl

/-- Schwartz inputs have genuine membership in every frozen weighted L² space. -/
theorem memLp_weighted_schwartz (s : ℝ) (f : 𝓢(Mom d, ℝ)) :
    MemLp (weightedFunction s f) 2 := by
  refine MemLp.ae_eq (Filter.Eventually.of_forall fun k => weightedSchwartzCLM_apply s f k)
    ((weightedSchwartzCLM s f).memLp 2)

/-- The canonical weighted embedding of Schwartz space into real L². -/
@[expose] def weightedToL2CLM (s : ℝ) :
    𝓢(Mom d, ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure (Mom d)) :=
  (SchwartzMap.toLpCLM ℝ ℝ 2 volume).comp (weightedSchwartzCLM s)

/-- Its L² representative is the exact weighted input almost everywhere. -/
theorem weightedToL2CLM_coeFn (s : ℝ) (f : 𝓢(Mom d, ℝ)) :
    (weightedToL2CLM s f : Mom d → ℝ) =ᵐ[volume] weightedFunction s f := by
  have h := (weightedSchwartzCLM s f).coeFn_toLp 2 volume
  exact h.trans (Filter.Eventually.of_forall fun k => weightedSchwartzCLM_apply s f k)

/-- The Banach-space norm of the embedding equals the frozen norm, without a change of weights. -/
theorem norm_weightedToL2CLM (s : ℝ) (f : 𝓢(Mom d, ℝ)) :
    ‖weightedToL2CLM s f‖ = weightedL2Norm s f := by
  let hmem := memLp_weighted_schwartz s f
  have heq : weightedToL2CLM s f = hmem.toLp (weightedFunction s f) := by
    apply Lp.ext
    exact (weightedToL2CLM_coeFn s f).trans hmem.coeFn_toLp.symm
  rw [heq, ← weightedL2Norm_eq_norm_toLp s f hmem]

end WaveTurbulence.WKEL2
