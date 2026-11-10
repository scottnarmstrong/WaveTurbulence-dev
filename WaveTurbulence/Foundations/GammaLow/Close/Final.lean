/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.GammaLow.Close.Halves
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.B4
public import WaveTurbulence.Foundations.GammaLow.Glue.Layergarden
public import WaveTurbulence.Foundations.GammaLow.Glue.Flower
public import WaveTurbulence.Foundations.GammaLow.Glue.Fixedpoint
public import WaveTurbulence.Foundations.GammaLow.Glue.Propansatz
public import WaveTurbulence.Foundations.GammaLow.Glue.Main

/-!
# The full range `0 < γ < 1`: the two `γ ≤ 1/2` halves closed, and the five full-range results (wt-orch)

`flower_low_closed` and `layergarden_low_closed` are the two `γ ≤ 1/2` halves with every input proved. Applying the L07
glue (`GammaLow.Glue`, whose conclusions are `Expr`-checked against the frozen anchors in `Glue.Exact`) gives the
full-range statements of `layergardenFlower_v4`, `layergarden`, `fixedpoint`, `propansatz` and `main`. These are the
provider terms for the five seals.
-/

@[expose] public section

set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Close

/-- **The flower low half, closed** (L8's marked stage 1 `stage1MKGateLow`). -/
theorem flower_low_closed : Flower.LayergardenFlowerLowGate :=
  flower_low_of_marked Flower.one_le_C₀L Flower.one_le_cθL Flower.stage1MKGateLow

end WaveTurbulence.GammaLow.Close
