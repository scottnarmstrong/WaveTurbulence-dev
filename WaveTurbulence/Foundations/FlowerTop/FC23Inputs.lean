/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FC23.Cut1Prefix

/-! Consume the posted FC3 analytic family input through the proved FC2 frozen-prefix reduction. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop

/-- Owner-exact pre-extraction uniform-family budget; no final cut1 estimate is assumed. -/
abbrev FC23UniformCut1Input := FC23.FC23UniformCut1At

/-- The FC2 reduction discharges all cut1 scale and numerical prefix conditions. -/
theorem fc23Cut1Prefix (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ)
    (hC : ∀ d, 0 < C d) (hU : ∀ P p, 0 < U P p)
    (hFC3 : WTPrefixP (FC23UniformCut1Input C U)) : WTPrefixP FC23.FC23Cut1At :=
  FC23.cut1_prefix_of_uniformFlowerFamily C U hC hU hFC3

end WaveTurbulence.FlowerTop
