/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapFinal
public import WaveTurbulence.Foundations.Flower.MkSlotsO.UnKind
public import WaveTurbulence.Foundations.Flower.MkSlotsO.PcKind
public import WaveTurbulence.Foundations.Flower.MkSlotsO.Assemble
public import WaveTurbulence.Foundations.Flower.ProtRT.RTGate

/-! # B3s-HELPER8: **`genSlotObligation`** — HELPER7's slot obligation, unconditional

`MkSlotsI.GenSlotObligation` (SlotObl rev 5, sha256 32790a0f…): the five work kinds of outer slots (`Split.lean`) —
cap pairs (`capKind`), unpinned slots (`unpinKind`), stem-protected chain slots (`stemProtChainKind`), and HELPER3's
off-stem root traces (`MkSlotsB.rtChainKind`, `MkSlotsB.protCplKind`) — combined by `genSlotObligation_of_three`
(`Assemble.lean`). The root traces rest on `RootTraceGate` (ruling R188/R189/F-RT-3, `RootTraceHyp.lean`, sha256
fbcc781d…), proved by RT-GATE (`ProtRT.rootTraceGate`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.Flower.MkSlotsO

/-- HELPER7's slot obligation from the off-stem root-trace gate. -/
theorem genSlotObligation_of_gate (hRT : RootTraceGate) : MkSlotsI.GenSlotObligation := by
  obtain ⟨K₁, hK₁, h₁⟩ := capKind
  obtain ⟨K₂, -, h₂⟩ := unpinKind
  obtain ⟨K₃, -, h₃⟩ := stemProtChainKind
  exact genSlotObligation_of_three hRT hK₁ h₁ h₂ h₃

/-- **HELPER7's slot obligation**, unconditional. -/
theorem genSlotObligation : MkSlotsI.GenSlotObligation :=
  genSlotObligation_of_gate ProtRT.rootTraceGate

end WaveTurbulence.Flower.MkSlotsO
