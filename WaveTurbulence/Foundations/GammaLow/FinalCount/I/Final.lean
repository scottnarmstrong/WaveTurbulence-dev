/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.I.Bridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.FinalCountClose
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.InputsLow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.ChainLowL
/-! # Row I: `FinalCountGateLow` from the ported run (packet L6, item I)

The ported stage-2 run (H, over the low family `Src γL`) proves the low half
`H.finalCount_half : [Src.LowInputs] → H.FinalCountGateHalf`, where `H.FinalCountGateHalf` is the restated
`WTPrefix fun P => P.γ ≤ 1/2 → H.FinalCountAt P` (H-MS2) and the η-choice is the restated `AsmPrefix` (H-ASM; no
`(2γ − 1)` constraint). The REG chain's ghost input is discharged inside the port (wt-l6ghost's
`Ghost.chainCoverLow'_holds`). `I.Bridge.finalCountGateLow_of_H` turns the low half into the gate. What remains is the
single field of `Src.LowInputs`, the LOW chain's ghost cover `H.ChainCoverLowL'` (RULING R194), proved by wt-l6ghost
(`Ghost.chainCoverLowL'_holds`): `finalCountGateLow` has no hypotheses. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount

/-- **`FinalCountGateLow`** under the H-LOW layer's input class. -/
theorem finalCountGateLow_of_lowInputs [Src.LowInputs] : FinalCountGateLow :=
  finalCountGateLow_of_H H.finalCount_half

/-- **`FinalCountGateLow`** from the LOW chain's ghost cover (the only remaining input). -/
theorem finalCountGateLow_of_ghost (hL : H.ChainCoverLowL') : FinalCountGateLow :=
  haveI : Src.LowInputs := ⟨hL⟩
  finalCountGateLow_of_lowInputs

/-- **The final-count gate at `0 < γ ≤ 1/2`** (packet L6), with no hypotheses. -/
theorem finalCountGateLow : FinalCountGateLow :=
  finalCountGateLow_of_ghost Ghost.chainCoverLowL'_holds

end WaveTurbulence.GammaLow.FinalCount
