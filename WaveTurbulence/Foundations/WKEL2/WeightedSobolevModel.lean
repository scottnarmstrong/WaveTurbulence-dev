/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedJets
public import WaveTurbulence.Foundations.WKEL2.DenseLinearExtension
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Complete weighted moment and derivative spaces

Complete the actual finite Schwartz jet image in its inherited supremum L²
norm. The resulting Banach space has an isometric realization in the product
of its L² jet coordinates, and Schwartz functions form a dense subspace.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped SchwartzMap

namespace WaveTurbulence.WKEL2

/-- The actual image of the finite weighted Schwartz jet. -/
@[expose] def weightedJetRange (d : ℕ) (s : ℝ) (m : ℕ) :
    Submodule ℝ (JetIndex d m → Lp ℝ 2 (volume : Measure (Mom d))) :=
  LinearMap.range (weightedJetCLM s m).toLinearMap

/-- The normed dense Schwartz core of a finite weighted jet space. -/
abbrev WeightedJetCore (d : ℕ) (s : ℝ) (m : ℕ) := ↥(weightedJetRange d s m)

/-- The complete weighted derivative and moment space, in finite jet coordinates. -/
abbrev WeightedSobolevSpace (d : ℕ) (s : ℝ) (m : ℕ) := Completion (WeightedJetCore d s m)

variable {d : ℕ}

/-- The faithful weighted jet identifies Schwartz functions with the dense normed core. -/
@[expose] def weightedJetCoreEquiv (s : ℝ) (m : ℕ) :
    𝓢(Mom d, ℝ) ≃ₗ[ℝ] WeightedJetCore d s m :=
  LinearEquiv.ofInjective (weightedJetCLM s m).toLinearMap (weightedJetCLM_injective s m)

/-- Continuous Schwartz-to-core jet embedding. -/
@[expose] def weightedJetCoreCLM (s : ℝ) (m : ℕ) :
    𝓢(Mom d, ℝ) →L[ℝ] WeightedJetCore d s m :=
  (weightedJetCLM s m).codRestrict (weightedJetRange d s m) (fun f => ⟨f, rfl⟩)

/-- Canonical dense linear isometry of the jet core into its completion. -/
@[expose] def weightedJetCoreInclusion (s : ℝ) (m : ℕ) :
    WeightedJetCore d s m →ₗᵢ[ℝ] WeightedSobolevSpace d s m := Completion.toComplₗᵢ

theorem denseRange_weightedJetCoreInclusion (s : ℝ) (m : ℕ) :
    DenseRange (weightedJetCoreInclusion (d := d) s m) := Completion.denseRange_coe

/-- The Schwartz embedding in the complete weighted moment and derivative space. -/
@[expose] def schwartzToWeightedSobolevCLM (s : ℝ) (m : ℕ) :
    𝓢(Mom d, ℝ) →L[ℝ] WeightedSobolevSpace d s m :=
  (weightedJetCoreInclusion s m).toContinuousLinearMap.comp (weightedJetCoreCLM s m)

/-- Schwartz density is part of the completion construction, not an additional assumption. -/
theorem denseRange_schwartzToWeightedSobolevCLM (s : ℝ) (m : ℕ) :
    DenseRange (schwartzToWeightedSobolevCLM (d := d) s m) := by
  have H := (denseRange_weightedJetCoreInclusion (d := d) s m).comp
    (weightedJetCoreEquiv (d := d) s m).surjective.denseRange
    (weightedJetCoreInclusion s m).continuous
  exact H

/-- The completed jet still has exactly its original finite supremum norm. -/
theorem norm_schwartzToWeightedSobolevCLM (s : ℝ) (m : ℕ) (f : 𝓢(Mom d, ℝ)) :
    ‖schwartzToWeightedSobolevCLM s m f‖ = ‖weightedJetCLM s m f‖ := by
  change ‖weightedJetCoreInclusion s m (weightedJetCoreCLM s m f)‖ = _
  rw [(weightedJetCoreInclusion s m).norm_map]
  rfl

/-- Recover the unique Schwartz representative of a core jet. -/
@[expose] def weightedJetCoreDecode (s : ℝ) (m : ℕ) :
    WeightedJetCore d s m →ₗ[ℝ] 𝓢(Mom d, ℝ) := (weightedJetCoreEquiv s m).symm.toLinearMap

end WaveTurbulence.WKEL2
