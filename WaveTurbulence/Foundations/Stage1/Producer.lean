/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD16
public import WaveTurbulence.Foundations.Spine.SourceProviders
public import WaveTurbulence.Foundations.Spine.SpineWithProviders
public import WaveTurbulence.Foundations.FinalCount.FinalCountClose
public import WaveTurbulenceVineParam.VineParamMain

/-! # The S2 Stage-1 producer on main, conditional on V5 (batch 4b-2)

`stage1ReductionGate_of_V5'` : `WTPrefix VineEstCanonLayerHalfMK → Stage1ReductionGate`, the S2 producer
`Represents.stage1ReductionGate_of_V5` with its other three inputs discharged by main's own theorems:
`WaveTurbulence.Vine.Param.vineparam` (M9) and `LGSpine.leafwise_incoherent_decay`,
`LGSpine.leafwise_coherent_approximation` (`Spine.SourceProviders`).  The only remaining input is V5's
kind-generic half-range estimate `VineEstCanonLayerHalfMK`.  `layergarden_v2_of_V5` composes it with batch 3's
`layergarden_v2_of_stage1_finalCount` and batch 5's unconditional `finalCount_half`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Spine
open WaveTurbulence.Induct

/-- Stage-1 reduction gate from V5's half-range estimate alone. -/
theorem stage1ReductionGate_of_V5' :
    WTPrefix VineEstS5C.VineEstCanonLayerHalfMK → LGSpine.Stage1ReductionGate := fun hV ↦
  Represents.stage1ReductionGate_of_V5 WaveTurbulence.Vine.Param.vineparam leafwise_incoherent_decay
    leafwise_coherent_approximation hV

/-- The frozen layergarden-v2 conclusion, conditional only on V5's half-range estimate. -/
theorem layergarden_v2_of_V5 :
    WTPrefix VineEstS5C.VineEstCanonLayerHalfMK → LGSpine.LayergardenV2Gate := fun h ↦
  layergarden_v2_of_stage1_finalCount (stage1ReductionGate_of_V5' h) FinalCountAsm.finalCount_half

end WaveTurbulence.Spine
