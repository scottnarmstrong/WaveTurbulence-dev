/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.S2ST.Stage1GateSTB2

/-! R97: the owner-exact both-member ST gate STB2 recovers the ordinary empty-anchor reduction (owner's bridge). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open LGSpine

/-- Empty anchors and stubs recover the native reduction from the literal S2-ST STB2 gate (owner's
`S2ST.stage1ReductionAt_of_STB2`). -/
theorem stage1ReductionAt_of_STB (C₀ : ℕ) (P : WTParams) (h : S2ST.Stage1ReductionAtSTB2 C₀ P) :
    Stage1ReductionAt C₀ P :=
  S2ST.stage1ReductionAt_of_STB2 C₀ P h

end WaveTurbulence.FlowerTop
