/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Measurability of the literal B1 source time domain -/

public section
namespace WaveTurbulence.IncohInst
open MeasureTheory

/-- All source layer, ancestor and lone-parent constraints form a measurable time domain. -/
theorem measurableSet_kDomain {w : ℕ} (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) : MeasurableSet (kDomain LG up s) := by
  classical
  unfold kDomain
  measurability

end WaveTurbulence.IncohInst
