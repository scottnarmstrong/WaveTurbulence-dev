/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.Gate
public import WaveTurbulence.Foundations.Flower.ProtRT.RT2Both

/-! # RT-GATE: **`MkSlotsO.RootTraceGate`**, unconditional

`rootTraceGate_of` (Gate.lean) with the both-pinned couple bound `rt2_both` (RT2Both.lean). -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.Flower.ProtRT

/-- **The off-stem root-trace gate** (ruling R188; HELPER8's `RootTraceHyp.lean`, sha256 fbcc781d…). -/
theorem rootTraceGate : MkSlotsO.RootTraceGate :=
  rootTraceGate_of fun _ h0 h1 h => rt2_both h0 h1 h

end WaveTurbulence.Flower.ProtRT
