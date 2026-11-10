/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Interpolation
public import Mathlib.Analysis.SpecificLimits.Basic
/-! TARGET L2253–2255: sum class bounds by their two discrete complexity parameters. -/
public section
namespace WaveTurbulence.LGSpine
open Finset

/-- Uniform finite geometric bound; no cutoff-dependent factor is lost. -/
theorem sum_powers_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (N : ℕ) :
    ∑ j ∈ range N, r ^ j ≤ 2 := by
  apply (sum_le_sum fun j _ => pow_le_pow_left₀ hr0 hr j).trans
  exact sum_geometric_two_le N

end WaveTurbulence.LGSpine
