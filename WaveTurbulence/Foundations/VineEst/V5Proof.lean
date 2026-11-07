/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.KindFinal.Export
public import WaveTurbulence.Foundations.Spine.SourceProviders
public import WaveTurbulence.Foundations.Stage1.Producer

/-! # V5 on main: the kind-generic VINEEST and `layergarden_v2` (batch 4b-3)

* `vineEstCanonLayerHalfMK : WTPrefix VineEstCanonLayerHalfMK` (TARGET Proposition `vineest`, L1742–L1749, half range,
  for G ∈ G_{p+1} or C_{p+1}): V5-KIND's `KindFinal.vineEstCanonLayerHalfMK_of_gates` applied to main's proved leafwise
  gates `Spine.leafwise_coherent_approximation` and `Spine.leafwise_incoherent_decay` (`Spine.SourceProviders`).  Its type
  is batch 4b-1's statement constant `VineEstS5C.VineEstCanonLayerHalfMK`, the hypothesis of batch 4b-2's
  `Spine.layergarden_v2_of_V5`.
* `layergarden_v2_proof : LGSpine.LayergardenV2Gate`, the type of the frozen anchor `layergarden_v2` token for token
  (`V2Chain.LayergardenV2Gate`, generated from the frozen file).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEst

/-- **VINEEST (ii), kind-generic, on main**: the half-range layer estimate over canonical objects, with no hypotheses. -/
theorem vineEstCanonLayerHalfMK : WTPrefix VineEstS5C.VineEstCanonLayerHalfMK :=
  VineEstS5C.P4.KindFinal.vineEstCanonLayerHalfMK_of_gates Spine.leafwise_coherent_approximation
    Spine.leafwise_incoherent_decay

/-- **`layergarden_v2`** (T Prop `layergarden`, L761–L779, `1/2 < γ < 1`): batch 4b-2's `layergarden_v2_of_V5` applied to
`vineEstCanonLayerHalfMK`. -/
theorem layergarden_v2_proof : LGSpine.LayergardenV2Gate :=
  Spine.layergarden_v2_of_V5 vineEstCanonLayerHalfMK

end WaveTurbulence.VineEst
