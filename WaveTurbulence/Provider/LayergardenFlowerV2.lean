/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CoupleSum
public import WaveTurbulence.Frozen.Defs.FixPat
public import WaveTurbulence.Frozen.Defs.FlowerKind
public import WaveTurbulence.Frozen.Defs.FlowerSum
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.InstDecidableEqFixPat
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RemainderBound
public import WaveTurbulence.Frozen.Defs.TreeKind
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefixP

/-!
# Provider for `WaveTurbulence.layergardenFlower_v2` (the γ ∈ (1/2, 1) successor, ruling D10)

The proof of the frozen anchor `WaveTurbulence.layergardenFlower_v2` (T Prop `flowerest1`, L2279–L2305; T L2306–L2338; WAVE-B v2 §4.15; T L2280; T (flowerest2); T (newnormn); T L2331; T L2312; T L2290) is assembled here under the export
`WaveTurbulence.Provider.layergardenFlower_v2`. Quarantined while the anchor is `DRAFT_SORRY`:
only the frozen anchor may import this module.
-/

public section
