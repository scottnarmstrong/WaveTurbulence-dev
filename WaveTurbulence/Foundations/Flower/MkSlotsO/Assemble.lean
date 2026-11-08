/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.Split
public import WaveTurbulence.Foundations.Flower.MkSlotsB.RTKind

/-! # B3s-HELPER8: the assembly with HELPER3's root-trace kinds

`genSlotObligation_of_three`: `MkSlotsI.GenSlotObligation` from `RootTraceGate` (through HELPER3's
`MkSlotsB.rtChainKind`, `MkSlotsB.protCplKind`, module `MkSlotsB.RTKind`) and the three remaining kinds: cap pairs,
unpinned slots, stem-protected chain slots. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.Flower.MkSlotsO

/-- **The slot obligation from the root-trace gate and the three remaining kinds.** -/
theorem genSlotObligation_of_three (hRT : RootTraceGate) {K₁ K₂ K₃ : ℕ → ℝ → ℝ} (hK₁ : ∀ d η, 1 ≤ K₁ d η)
    (hcap : WTPrefix (GenSlotOnAt IsCapSlot K₁)) (hun : WTPrefix (GenSlotOnAt IsUnpinSlot K₂))
    (hstem : WTPrefix (GenSlotOnAt IsStemProtChainSlot K₃)) : MkSlotsI.GenSlotObligation := by
  obtain ⟨K₄, -, h₄⟩ := MkSlotsB.rtChainKind hRT
  obtain ⟨K₅, -, h₅⟩ := MkSlotsB.protCplKind hRT
  exact genSlotObligation_of_split hK₁ hcap hun (protChainKind_of h₄ hstem) h₅

end WaveTurbulence.Flower.MkSlotsO
