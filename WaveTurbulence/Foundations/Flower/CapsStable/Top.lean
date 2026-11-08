/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CapsStable.Batch
public import WaveTurbulence.Foundations.Flower.CapsComp.Top

/-! # CAPS-STABLE: the flower estimate from the per-component bound

`flower_v3_of_marked`: A3b's composite `flower_v3_of_marked_of_stable` with its named input discharged by
`capsTwistStable`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.CapsStable

/-- **The flower gate from the marked component bound.** -/
theorem flower_v3_of_marked (B : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 24000)
    (hM : WTPrefixP (MarkedComponentBoundAtI B)) : V2Chain.LayergardenFlowerV3Gate :=
  CapsComp.flower_v3_of_marked_of_stable capsTwistStable B hB0 hB hM

end WaveTurbulence.Flower.CapsStable
