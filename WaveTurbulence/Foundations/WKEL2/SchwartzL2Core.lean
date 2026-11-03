/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.SchwartzWeightInverse

/-!
# The dense weighted-Schwartz core inside the L² Banach model

The range has its inherited L² norm. Its linear inverse to Schwartz space
is well defined by the proved injectivity of the exact weighted embedding.
This is the normed dense domain used to extend the collision map.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

/-- The actual weighted Schwartz image inside ordinary L². -/
@[expose] def weightedSchwartzRange (d : ℕ) (s : ℝ) : Submodule ℝ (Lp ℝ 2 (volume : Measure (Mom d))) :=
  LinearMap.range (weightedToL2CLM s).toLinearMap

/-- The normed weighted-Schwartz core, with norm inherited from the exact weighted embedding. -/
abbrev WeightedSchwartzCore (d : ℕ) (s : ℝ) := ↥(weightedSchwartzRange d s)

variable {d : ℕ}

/-- The faithful weighted embedding identifies Schwartz space linearly with its range. -/
@[expose] def weightedSchwartzCoreEquiv (s : ℝ) : 𝓢(Mom d, ℝ) ≃ₗ[ℝ] WeightedSchwartzCore d s :=
  LinearEquiv.ofInjective (weightedToL2CLM s).toLinearMap (weightedToL2CLM_injective s)

/-- Isometric inclusion of the dense weighted-Schwartz core. -/
@[expose] def weightedSchwartzCoreInclusion (s : ℝ) :
    WeightedSchwartzCore d s →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (Mom d)) where
  toLinearMap := (weightedSchwartzRange d s).subtype
  norm_map' _ := rfl

theorem weightedSchwartzCoreInclusion_equiv (s : ℝ) (f : 𝓢(Mom d, ℝ)) :
    weightedSchwartzCoreInclusion s (weightedSchwartzCoreEquiv s f) = weightedToL2CLM s f := rfl

/-- The core inclusion has dense range in the complete weighted L² model. -/
theorem denseRange_weightedSchwartzCoreInclusion (s : ℝ) :
    DenseRange (weightedSchwartzCoreInclusion (d := d) s) := by
  intro u
  have hsub : Set.range (weightedToL2CLM (d := d) s) ⊆
      Set.range (weightedSchwartzCoreInclusion s) := by
    rintro v ⟨f, rfl⟩
    exact ⟨weightedSchwartzCoreEquiv s f, rfl⟩
  exact (closure_mono hsub) (denseRange_weightedToL2CLM s u)

/-- Recover the unique Schwartz input of a core element. -/
@[expose] def weightedSchwartzCoreDecode (s : ℝ) : WeightedSchwartzCore d s →ₗ[ℝ] 𝓢(Mom d, ℝ) :=
  (weightedSchwartzCoreEquiv s).symm.toLinearMap

theorem weightedToL2CLM_coreDecode (s : ℝ) (u : WeightedSchwartzCore d s) :
    weightedToL2CLM s (weightedSchwartzCoreDecode s u) = (u : Lp ℝ 2 volume) := by
  have h := (weightedSchwartzCoreEquiv s).apply_symm_apply u
  exact congrArg Subtype.val h

/-- The core norm is exactly the frozen weighted norm of the decoded Schwartz function. -/
theorem weightedL2Norm_coreDecode (s : ℝ) (u : WeightedSchwartzCore d s) :
    weightedL2Norm s (weightedSchwartzCoreDecode s u) = ‖u‖ := by
  rw [← norm_weightedToL2CLM, weightedToL2CLM_coreDecode]
  rfl

end WaveTurbulence.WKEL2
