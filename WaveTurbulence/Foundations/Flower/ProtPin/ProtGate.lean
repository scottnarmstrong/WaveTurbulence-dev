/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.GateT2a
public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2ATrace

/-! # D3 PROT-PIN: `ProtBoundGate`

**`protBoundGate : ProtBoundGate`** (ProtDefs' `ProtBoundGate := WTPrefix ProtBoundAt`, R172/R176), unconditional:
`protBoundGate_of_t2a` applied to the (a+) root trace `tc2a_trace` (D3-HELPER). -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-- **D3 PROT-PIN: every pinned protected object** (ProtDefs' `ProtBoundGate`). -/
theorem protBoundGate : ProtBoundGate :=
  protBoundGate_of_t2a fun _ h0 h1 => tc2a_trace h0 h1

end WaveTurbulence.Flower.ProtPin
