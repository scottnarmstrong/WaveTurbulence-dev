/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.DecompG
public import WaveTurbulence.Foundations.Flower.MkAsm.Top
/-! # A3b CAPS-COMP: the composite to the frozen gate

`flower_v3_of_marked_of_stable`: with the label twist stability `CapsTwistStable` (the distinctly named input of
`Classes.lean`), `WTPrefixP (MarkedComponentBoundAtI B) → LayergardenFlowerV3Gate`, through MK-ASM's
`flower_v3_of_marked_of_caps` and the discharged helpers `capsDecompF_of_stable`, `capsDecompG_of_stable`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkAsm

/-- **The composite** (conditional on the label twist stability). -/
theorem flower_v3_of_marked_of_stable (hst : CapsTwistStable) (B : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 24000)
    (hM : WTPrefixP (MarkedComponentBoundAtI B)) : V2Chain.LayergardenFlowerV3Gate :=
  flower_v3_of_marked_of_caps (capsDecompF_of_stable hst) (capsDecompG_of_stable hst) B hB0 hB hM

end WaveTurbulence.Flower.CapsComp
