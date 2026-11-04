/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CoupleRemainder
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.IsBalancedSig
public import WaveTurbulence.Frozen.Defs.JbrProd
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RemainderBound
public import WaveTurbulence.Frozen.Defs.SNorm
public import WaveTurbulence.Frozen.Defs.TruncSum
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTParamsR
public import WaveTurbulence.Frozen.Defs.WTParamsTheta
public import WaveTurbulence.Frozen.Defs.WTPrefix

/-!
# Provider for `WaveTurbulence.layergarden`

The proof of the frozen anchor `WaveTurbulence.layergarden` (T Prop `layergarden`, L761–L779; T L776; WAVE-B v2 §4.2; T L762) is assembled here under the export
`WaveTurbulence.Provider.layergarden`. Quarantined while the anchor is `DRAFT_SORRY`:
only the frozen anchor may import this module.
-/

public section
