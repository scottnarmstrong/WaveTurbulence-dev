/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.GateL
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.MolecularSpineAt
/-! # Row I: the ported gate body is L6's `γL` gate body (packet L6, item I)

The port of main's `Spine.MolecularSpineAt` (`H.FinalCountAt`, over `Src.CountingChoices Src.γL`) is by definition L6's
`FinalCountLAt`. So the restated `H.FinalCountGateHalf := WTPrefix fun P => P.γ ≤ 1/2 → H.FinalCountAt P` (H-MS2,
`H/Spine/SpineInputsV2`) is the hypothesis of `finalCountGateLow_of_L`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount

/-- **`FinalCountGateLow` from the ported run's low half** (`H.FinalCountGateHalf`, restated for `γ ≤ 1/2`). -/
theorem finalCountGateLow_of_H (h : WTPrefix fun P => P.γ ≤ 1 / 2 → H.FinalCountAt P) : FinalCountGateLow :=
  finalCountGateLow_of_L h

end WaveTurbulence.GammaLow.FinalCount
