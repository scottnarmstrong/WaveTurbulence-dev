/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.GammaLow.LGLow.Assembly
public import WaveTurbulence.Foundations.GammaLow.Flower.Assembly
public import WaveTurbulence.Foundations.GammaLow.FinalCount.I.Final
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.ChainLowL
public import WaveTurbulence.Foundations.GammaLow.Famc.Coarse.Gate
public import WaveTurbulence.Foundations.TVine.Struct.Final
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Final

/-!
# The two `γ ≤ 1/2` halves, with every proved input discharged (wt-orch, final assembly)

The halves consumed by the L07 glue (`GammaLow.Glue`): the layergarden low half `LGLow.LayergardenLowGate` and the
flower low half `Flower.LayergardenFlowerLowGate`. Here every input that is already proved is discharged:
- the final-count gate `FinalCountGateLow` (L6, with the two run-wide ghost covers of wt-l6ghost);
- L5c's coarse spliced gate;
- L3's sub-object theorem (Theorem 1.15);
- the marked count (L8-H2).
Only the inputs whose proofs are still being assembled remain as hypotheses: L5a's stage-1 gate and, for the flower,
L8's marked stage 1. When those land, `Close.Final` applies these lemmas to them.
-/

@[expose] public section

set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Close

/-- The `γ ≤ 1/2` final-count gate: L6's row I applied to wt-l6ghost's LOW chain cover (the REG one is already
discharged inside `finalCountGateLow_of_ghost`). -/
theorem finalCountGateLow_proved : FinalCount.FinalCountGateLow :=
  FinalCount.finalCountGateLow_of_ghost FinalCount.Ghost.chainCoverLowL'_holds

/-- The layergarden low half, given only L5a's stage-1 gate. -/
theorem layergarden_low_of_stage1 (h5a : Fama.Stage1ReductionGateLow) : LGLow.LayergardenLowGate :=
  LGLow.layergarden_low h5a Famc.coarseSplicedGateLow finalCountGateLow_proved TVine.Struct.subObjects_holds.{0, 0}

/-- The flower low half, given only L5a's stage-1 gate and L8's marked stage 1. -/
theorem flower_low_of_stage1 {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (h5a : Fama.Stage1ReductionGateLow) (hI : Flower.Stage1MKGateLow C₀ 452 cθ) :
    Flower.LayergardenFlowerLowGate :=
  Flower.flowerest1_low_of_items5 hC₀ hcθ h5a hI Flower.H2.finalCountAtMKLAt_holds

end WaveTurbulence.GammaLow.Close
