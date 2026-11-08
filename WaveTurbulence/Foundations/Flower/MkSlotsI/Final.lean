/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.Prefix
public import WaveTurbulence.Foundations.Flower.MkSlotsO.GenSlot

/-! # B3s-HELPER7 AsmG (8): the unconditional exports

* **`classRepGen_prefix : WTPrefix (MkSlotsG.ClassRepGen 452)`**: `classRepGen_prefix_of` (W:MkSlotsI/Prefix.lean) at
  HELPER8's proved slot obligation `MkSlotsO.genSlotObligation` (W:MkSlotsO/GenSlot.lean);
* `markedClassRepresentsMK_prefix`: B4's hypothesis `MarkedClassRepresentsMK 452 cθ` on the prefix for
  `cθGen ≤ cθ` (helper 6's bridge `MkSlotsG.markedClassRepresentsMK_prefix_of_repGen`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence.Induct WaveTurbulence.LGSpine

namespace WaveTurbulence.Flower.MkSlotsI

/-- **The analytic core of B3s on the prefix** (hypothesis-free). -/
theorem classRepGen_prefix : WTPrefix (MkSlotsG.ClassRepGen 452) :=
  classRepGen_prefix_of MkSlotsO.genSlotObligation

/-- **B4's marked class hypothesis on the prefix** for `cθGen ≤ cθ` (hypothesis-free). -/
theorem markedClassRepresentsMK_prefix {cθ : ℝ} (hθ : MkSlotsG.cθGen ≤ cθ) :
    WTPrefix (Stage1MKGate.MarkedClassRepresentsMK 452 cθ) :=
  MkSlotsG.markedClassRepresentsMK_prefix_of_repGen hθ classRepGen_prefix

end WaveTurbulence.Flower.MkSlotsI
