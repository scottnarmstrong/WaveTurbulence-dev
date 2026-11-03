/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzWeightedL2

/-!
# Inverse weights and density of weighted Schwartz data in L²
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Positive and negative frozen weights cancel exactly. -/
theorem weightedFunction_neg_cancel (s : ℝ) (f : Mom d → ℝ) (k : Mom d) :
    weightedFunction s (weightedFunction (-s) f) k = f k := by
  dsimp only [weightedFunction]
  rw [← mul_assoc, ← Real.rpow_add (by positivity), show s / 2 + (-s) / 2 = 0 by ring,
    Real.rpow_zero, one_mul]

/-- Multiplication by the negative weight is the inverse on Schwartz space. -/
theorem weightedSchwartzCLM_neg_cancel (s : ℝ) (f : 𝓢(Mom d, ℝ)) :
    weightedSchwartzCLM s (weightedSchwartzCLM (-s) f) = f := by
  ext k
  rw [weightedSchwartzCLM_apply]
  dsimp only [weightedFunction]
  rw [weightedSchwartzCLM_apply]
  exact weightedFunction_neg_cancel s f k

theorem weightedSchwartzCLM_surjective (s : ℝ) : Function.Surjective (weightedSchwartzCLM (d := d) s) :=
  fun f => ⟨weightedSchwartzCLM (-s) f, weightedSchwartzCLM_neg_cancel s f⟩

theorem weightedSchwartzCLM_injective (s : ℝ) : Function.Injective (weightedSchwartzCLM (d := d) s) := by
  have hleft : Function.LeftInverse (weightedSchwartzCLM (d := d) (-s)) (weightedSchwartzCLM s) := by
    intro f
    simpa only [neg_neg] using weightedSchwartzCLM_neg_cancel (-s) f
  exact hleft.injective

/-- The weighted Schwartz embedding has dense range in its Banach L² model. -/
theorem denseRange_weightedToL2CLM (s : ℝ) : DenseRange (weightedToL2CLM (d := d) s) := by
  have h := (SchwartzMap.denseRange_toLpCLM (E := Mom d) (F := ℝ)
    (p := 2) (μ := volume) ENNReal.ofNat_ne_top).comp
      (weightedSchwartzCLM_surjective s).denseRange (SchwartzMap.toLpCLM ℝ ℝ 2 volume).continuous
  simpa only [weightedToL2CLM, ContinuousLinearMap.coe_comp] using h

/-- The weighted Schwartz embedding is faithful. -/
theorem weightedToL2CLM_injective (s : ℝ) : Function.Injective (weightedToL2CLM (d := d) s) := by
  intro f g h
  apply weightedSchwartzCLM_injective s
  apply SchwartzMap.injective_toLp 2 (volume : Measure (Mom d))
  exact h

/-- A frozen Schwartz solution gives a continuous curve in the weighted Banach model. -/
theorem continuousOn_weightedToL2CLM_of_isWKESolution (s : ℝ)
    {f₀ : 𝓢(Mom d, ℝ)} {T : ℝ} {φ : ℝ → 𝓢(Mom d, ℝ)}
    (hφ : IsWKESolution f₀ T φ) :
    ContinuousOn (fun t => weightedToL2CLM s (φ t)) (Set.Icc 0 T) :=
  (weightedToL2CLM s).continuous.comp_continuousOn hφ.1

end WaveTurbulence.WKEL2
