/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntPrefix
public import WaveTurbulence.Foundations.Flower.MkSlots.CapObl

/-! # B3s MK-SLOTS (integration, final): the hypothesis-free α exports

`classRepAlphaJ_prefix'` and `markedClassRepresentsMKαJ_prefix'`: `classRepAlphaJ_prefix` and
`markedClassRepresentsMKαJ_prefix` applied to the proved cap-slot obligation `capSlotObligation` (`CapObl`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.MkSlots
open WaveTurbulence.Induct WaveTurbulence.LGSpine


/-- **`ClassRepAlphaJ cP` on the prefix** for `37 ≤ cP` (hypothesis-free). -/
theorem classRepAlphaJ_prefix' (cP : ℝ) (hcP : 37 ≤ cP) : WTPrefix (ClassRepAlphaJ cP) :=
  classRepAlphaJ_prefix cP hcP capSlotObligation

/-- **Milestone α with `|J| = R` on the prefix** for `37 ≤ cP` (hypothesis-free). -/
theorem markedClassRepresentsMKαJ_prefix' (cP cθ : ℝ) (hcP : 37 ≤ cP) :
    WTPrefix (MarkedClassRepresentsMKαJ cP cθ) :=
  markedClassRepresentsMKαJ_prefix cP cθ hcP capSlotObligation

end WaveTurbulence.Flower.MkSlots
